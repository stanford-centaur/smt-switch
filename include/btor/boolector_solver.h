#ifndef SMT_BOOLECTOR_SOLVER_H
#define SMT_BOOLECTOR_SOLVER_H

#include <memory>
#include <string>
#include <vector>

#include "boolector_func.h"
#include "boolector_sort.h"
#include "boolector_term.h"
#include "exceptions.h"
#include "solver.h"
#include "sort.h"

namespace smt
{
  /**
     Boolector Solver implementation
   */
class BoolectorSolver : public AbsSmtSolver
{
 public:
  // might have to use std::unique_ptr<Btor>(boolector_new) and move it?
  BoolectorSolver() : btor(boolector_new()){};
  BoolectorSolver(const BoolectorSolver&) = delete;
  BoolectorSolver& operator=(const BoolectorSolver&) = delete;
  ~BoolectorSolver() { boolector_delete(btor); };
  void set_opt(const std::string option, bool value) const override
  {
    if ((option == "produce-models") && value)
    {
      boolector_set_opt(btor, BTOR_OPT_MODEL_GEN, 1);
    }
    else
    {
      std::string msg = option;
      msg += " is not implemented for boolector.";
      throw NotImplementedException(msg.c_str());
    }
  }
  void set_opt(const std::string option, const std::string value) const override
  {
    throw NotImplementedException("String value for set_opt unimplemented");
  }
  Sort declare_sort(const std::string name, unsigned int arity) const override
  {
    throw IncorrectUsageException("Can't declare sorts with Boolector");
  }
  Term declare_const(const std::string name, Sort sort) const override
  {
    // TODO handle arrays correctly (need boolector_array instead of
    // boolector_var)
    std::shared_ptr<BoolectorSortBase> bs =
        std::static_pointer_cast<BoolectorSortBase>(sort);

    BoolectorNode * n;
    if (sort->get_kind() != ARRAY)
    {
      n = boolector_var(btor, bs->sort, name.c_str());
    }
    else
    {
      n = boolector_array(btor, bs->sort, name.c_str());
    }

    // note: giving the symbol a null Op
    Term term(new BoolectorTerm(btor,
                                n,
                                std::vector<Term>{},
                                Op()));
    return term;
  }
  // TODO implement declare_fun
  Func declare_fun(const std::string name,
                   const std::vector<Sort>& sorts,
                   Sort sort) const override
  {
    if (sorts.size() == 0)
    {
      throw IncorrectUsageException(
          "API does not support zero arity functions with declare_fun, please "
          "use declare_const");
    }
    else
    {
      std::vector<BoolectorSort> btor_domain_sorts;
      btor_domain_sorts.reserve(sorts.size());
      std::shared_ptr<BoolectorSortBase> bsort;
      for (Sort s : sorts)
      {
        bsort = std::static_pointer_cast<BoolectorSortBase>(s);
        btor_domain_sorts.push_back(bsort->sort);
      }

      // now the codomain sort
      bsort = std::static_pointer_cast<BoolectorSortBase>(sort);
      BoolectorSort btor_codomain_sort = bsort->sort;
      BoolectorSort btor_fun_sort = boolector_fun_sort(
          btor, &btor_domain_sorts[0], sorts.size(), btor_codomain_sort);
      BoolectorNode* n = boolector_uf(btor, btor_fun_sort, name.c_str());
      // uf_sort owns btor_fun_sort
      Sort uf_sort(new BoolectorUFSort(btor, btor_fun_sort, sorts, sort));
      Func f(new BoolectorFunc(btor, n, uf_sort));
      return f;
    }
  }
  Term make_const(unsigned int i, Sort sort) const override
  {
    std::shared_ptr<BoolectorSortBase> bs =
        std::static_pointer_cast<BoolectorSortBase>(sort);
    // note: give the constant value a null PrimOp
    Term term(new BoolectorTerm(
        btor, boolector_int(btor, i, bs->sort), std::vector<Term>{}, Op()));
    return term;
  }
  void assert_formula(const Term& t) const override
  {
    std::shared_ptr<BoolectorTerm> bt =
        std::static_pointer_cast<BoolectorTerm>(t);
    boolector_assert(btor, bt->node);
  }
  bool check_sat() const override
  {
    return (BOOLECTOR_SAT == boolector_sat(btor));
  };
  Term get_value(Term& t) const override
  {
    Term result;
    std::shared_ptr<BoolectorTerm> bt =
        std::static_pointer_cast<BoolectorTerm>(t);
    Kind k = t->get_sort()->get_kind();
    if ((k == BV) || (k == BOOL))
    {
      const char* assignment = boolector_bv_assignment(btor, bt->node);
      BoolectorNode* bc = boolector_const(btor, assignment);
      boolector_free_bv_assignment(btor, assignment);
      // note: give the constant value a null PrimOp
      result = std::make_shared<BoolectorTerm>(
          btor, bc, std::vector<Term>{}, NUM_OPS_AND_NULL);
    }
    else if (k == ARRAY)
    {
      throw NotImplementedException("Array models unimplemented.");
    }
    else if (k == UNINTERPRETED)
    {
      throw NotImplementedException("UF models unimplemented.");
    }
    else
    {
      std::string msg("Can't get value for term with kind = ");
      msg += to_string(k);
      throw IncorrectUsageException(msg.c_str());
    }
    return result;
  }
  Sort make_sort(Kind k) const override
  {
    if (k == BOOL)
    {
      Sort s(new BoolectorBVSort(btor, boolector_bool_sort(btor), 1));
      return s;
    }
    else
    {
      std::string msg("Boolector does not support ");
      msg += to_string(k);
      throw NotImplementedException(msg.c_str());
    }
  }
  Sort make_sort(Kind k, unsigned int size) const override
  {
    if (k == BV)
    {
      Sort s(
          new BoolectorBVSort(btor, boolector_bitvec_sort(btor, size), size));
      return s;
    }
    else
    {
      std::string msg("Can't create Kind ");
      msg += to_string(k);
      msg += " with int argument.";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  Sort make_sort(Kind k, Sort idxsort, Sort elemsort) const override
  {
    if (k == ARRAY)
    {
      std::shared_ptr<BoolectorSortBase> btor_idxsort =
          std::static_pointer_cast<BoolectorSortBase>(idxsort);
      std::shared_ptr<BoolectorSortBase> btor_elemsort =
          std::static_pointer_cast<BoolectorSortBase>(elemsort);
      BoolectorSort bs =
          boolector_array_sort(btor, btor_idxsort->sort, btor_elemsort->sort);
      Sort s(new BoolectorArraySort(btor, bs, idxsort, elemsort));
      return s;
    }
    else
    {
      std::string msg("Can't create Kind ");
      msg += to_string(k);
      msg += " with two sort arguments.";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  Sort make_sort(Kind k, std::vector<Sort> sorts, Sort sort) const override
  {
    if (k == UNINTERPRETED)
    {
      int arity = sorts.size();
      std::vector<BoolectorSort> btor_sorts(arity);
      for (auto s : sorts)
      {
        std::shared_ptr<BoolectorSortBase> bs =
            std::static_pointer_cast<BoolectorSortBase>(s);
        btor_sorts.push_back(bs->sort);
      }
      std::shared_ptr<BoolectorSortBase> btor_sort =
          std::static_pointer_cast<BoolectorSortBase>(sort);
      BoolectorSort btor_fun_sort =
          boolector_fun_sort(btor, &btor_sorts[0], arity, btor_sort->sort);
      Sort s(new BoolectorUFSort(btor, btor_fun_sort, sorts, sort));
      return s;
    }
    else
    {
      std::string msg("Can't create Kind ");
      msg += to_string(k);
      msg += " with a vector of sorts and a sort";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  Term apply_func(PrimOp op, Term t) const override
  {
    try
    {
      std::shared_ptr<BoolectorTerm> bt =
          std::static_pointer_cast<BoolectorTerm>(t);
      BoolectorNode* result = unary_ops.at(op)(btor, bt->node);
      Term term(new BoolectorTerm(btor, result, std::vector<Term>{t}, op));
      return term;
    }
    catch (std::out_of_range o)
    {
      std::string msg("Can't apply ");
      msg += to_string(op);
      msg += " to a single term.";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  Term apply_func(PrimOp op, Term t0, Term t1) const override
  {
    try
    {
      std::shared_ptr<BoolectorTerm> bt0 =
          std::static_pointer_cast<BoolectorTerm>(t0);
      std::shared_ptr<BoolectorTerm> bt1 =
          std::static_pointer_cast<BoolectorTerm>(t1);
      BoolectorNode* result = binary_ops.at(op)(btor, bt0->node, bt1->node);
      Term term(new BoolectorTerm(btor, result, std::vector<Term>{t0, t1}, op));
      return term;
    }
    catch (std::out_of_range o)
    {
      std::string msg("Can't apply ");
      msg += to_string(op);
      msg += " to a single term.";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  Term apply_func(PrimOp op, Term t0, Term t1, Term t2) const override
  {
    try
    {
      std::shared_ptr<BoolectorTerm> bt0 =
          std::static_pointer_cast<BoolectorTerm>(t0);
      std::shared_ptr<BoolectorTerm> bt1 =
          std::static_pointer_cast<BoolectorTerm>(t1);
      std::shared_ptr<BoolectorTerm> bt2 =
          std::static_pointer_cast<BoolectorTerm>(t2);
      BoolectorNode* result =
          ternary_ops.at(op)(btor, bt0->node, bt1->node, bt2->node);
      Term term(
          new BoolectorTerm(btor, result, std::vector<Term>{t0, t1, t2}, op));
      return term;
    }
    catch (std::out_of_range o)
    {
      std::string msg("Can't apply ");
      msg += to_string(op);
      msg += " to a single term.";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  Term apply_func(PrimOp op, std::vector<Term> terms) const override
  {
    unsigned int size = terms.size();
    // binary ops are most common, check this first
    if (size == 2)
    {
      return apply_func(op, terms[0], terms[1]);
    }
    else if (size == 1)
    {
      return apply_func(op, terms[0]);
    }
    else if (size == 3)
    {
      return apply_func(op, terms[0], terms[1], terms[2]);
    }
    else
    {
      std::string msg("There's no primitive op of arity ");
      msg += std::to_string(size);
      msg += ".";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  Term apply_func(Op op, Term t) const override
  {
    if (op.num_idx == 0)
    {
      return apply_func(op.prim_op, t);
    }
    else
    {
      std::shared_ptr<BoolectorTerm> bt =
        std::static_pointer_cast<BoolectorTerm>(t);
      Term term;
      if (op.prim_op == Extract)
      {
        BoolectorNode* slice = boolector_slice(btor, bt->node, op.idx0, op.idx1);
        term = Term(new BoolectorTerm(btor, slice, std::vector<Term>{t}, Extract));
      }
      else if (op.prim_op == Zero_Extend)
      {
        BoolectorNode* uext = boolector_uext(btor, bt->node, op.idx0);
        term = Term(new BoolectorTerm(btor, uext, std::vector<Term>{t}, Zero_Extend));
      }
      else if (op.prim_op == Sign_Extend)
      {
        BoolectorNode* sext = boolector_sext(btor, bt->node, op.idx0);
        term = Term(new BoolectorTerm(btor, sext, std::vector<Term>{t}, Sign_Extend));
      }
      else
      {
        std::string msg = "Could not find Boolector implementation of ";
        msg += to_string(op.prim_op);
        throw IncorrectUsageException(msg.c_str());
      }
      return term;
    }
  }
  Term apply_func(Op op, Term t0, Term t1) const override
  {
    if (op.num_idx == 0)
    {
      return apply_func(op.prim_op, t0, t1);
    }
    else
    {
      throw IncorrectUsageException(
          "There are no supported indexed operators that take more than one "
          "argument");
    }
  }
  Term apply_func(Op op, Term t0, Term t1, Term t2) const override
  {
    if (op.num_idx == 0)
    {
      return apply_func(op.prim_op, t0, t1, t2);
    }
    else
    {
      throw IncorrectUsageException(
          "There are no supported indexed operators that take more than one "
          "argument");
    }
  }
  Term apply_func(Op op, std::vector<Term> terms) const override
  {
    if (op.num_idx == 0)
    {
      return apply_func(op.prim_op, terms);
    }
    else
    {
      if (terms.size() == 1)
      {
        return apply_func(op, terms[0]);
      }
      else
      {
        throw IncorrectUsageException(
            "There are no supported indexed operators that take more than one "
            "argument");
      }
    }
  }
  Term apply_func(Func f, Term t) const override
  {
    if (f->is_op())
    {
      Op op = f->get_op();
      if (op.num_idx == 0)
      {
        return apply_func(op.prim_op, t);
      }
      else
      {
        return apply_func(op, std::vector<Term>{t});
      }
    }
    else
    {
      // rely on the function application in the vector implementation
      return apply_func(f, std::vector<Term>{t});
    }
  }
  Term apply_func(Func f, Term t0, Term t1) const override
  {
    if (f->is_op())
    {
      Op op = f->get_op();
      if (op.num_idx == 0)
      {
        return apply_func(op.prim_op, t0, t1);
      }
      else
      {
        throw IncorrectUsageException(
            "No indexed operators that take two arguments");
      }
    }
    else
    {
      // rely on the function application in the vector implementation
      return apply_func(f, std::vector<Term>{t0, t1});
    }
  }
  Term apply_func(Func f, Term t0, Term t1, Term t2) const override
  {
    if (f->is_op())
    {
      Op op = f->get_op();
      if (op.num_idx == 0)
      {
        return apply_func(op.prim_op, t0, t1, t2);
      }
      else
      {
        throw IncorrectUsageException(
            "No indexed operators that take three arguments");
      }
    }
    else
    {
      // rely on the function application in the vector implementation
      return apply_func(f, std::vector<Term>{t0, t1, t2});
    }
  }
  Term apply_func(Func f, std::vector<Term> terms) const override
  {
    unsigned int size = terms.size();
    // Optimization: translate Op to PrimOp as early as possible to prevent
    // unpacking it multipe times
    if (f->is_op())
    {
      Op op = f->get_op();
      if (op.num_idx == 0)
      {
        return apply_func(op.prim_op, terms);
      }
      else
      {
        return apply_func(op, terms);
      }
    }
    else if (f->is_uf())
    {
      std::shared_ptr<BoolectorFunc> bf =
          std::static_pointer_cast<BoolectorFunc>(f);
      std::vector<BoolectorNode*> args;
      std::shared_ptr<BoolectorTerm> bt;
      for (auto t : terms)
      {
        bt = std::static_pointer_cast<BoolectorTerm>(t);
        args.push_back(bt->node);
      }
      BoolectorNode* result = boolector_apply(btor, &args[0], size, bf->node);
      Term term(new BoolectorTerm(btor, result, terms, f));
      return term;
    }

    std::string msg("Can't find any matching ops to apply to ");
    msg += std::to_string(size);
    msg += " terms.";
    throw IncorrectUsageException(msg.c_str());
  }

 protected:
  Btor* btor;
  };
}

#endif
