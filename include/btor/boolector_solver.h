#ifndef SMT_BOOLECTOR_SOLVER_H
#define SMT_BOOLECTOR_SOLVER_H

#include <memory>
#include <string>
#include <vector>

#include "boolector_uf.h"
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
    BoolectorSolver() : btor(boolector_new()) {};
    BoolectorSolver(const BoolectorSolver&) = delete;
    BoolectorSolver& operator=(const BoolectorSolver&) = delete;
    ~BoolectorSolver() { boolector_delete(btor); };
    void set_opt(const std::string option, bool value) const override {
      if ((option == "produce-models") && value) {
        boolector_set_opt(btor, BTOR_OPT_MODEL_GEN, 1);
      } else {
        std::string msg = option;
        msg += " is not implemented for boolector.";
        throw NotImplementedException(msg.c_str());
      }
    }
    void set_opt(const std::string option,
                 const std::string value) const override {
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
      Term term(new BoolectorTerm(btor,
                                  boolector_var(btor, bs->sort, name.c_str()),
                                  std::vector<Term>{}, VAR));
      return term;
    }
    // TODO implement declare_fun
    Term make_const(unsigned int i, Sort sort) const override {
      std::shared_ptr<BoolectorSortBase> bs =
          std::static_pointer_cast<BoolectorSortBase>(sort);
      Term term(new BoolectorTerm(btor, boolector_int(btor, i, bs->sort),
                                  std::vector<Term>{}, CONST));
      return term;
    }
    void assert_formula(const Term &t) const override {
      std::shared_ptr<BoolectorTerm> bt = std::static_pointer_cast<BoolectorTerm>(t);
      boolector_assert(btor, bt->node);
    }
    bool check_sat() const override {
      return (BOOLECTOR_SAT == boolector_sat(btor));
    };
    Term get_value(Term &t) const override {
      Term result;
      std::shared_ptr<BoolectorTerm> bt =
          std::static_pointer_cast<BoolectorTerm>(t);
      Kind k = t->get_sort()->get_kind();
      if ((k == BV) || (k == BOOL)) {
        BoolectorNode *bc =
            boolector_const(btor, boolector_bv_assignment(btor, bt->node));
        result = std::make_shared<BoolectorTerm>(btor, bc, std::vector<Term>{},
                                                 CONST);
      } else if (k == ARRAY) {
        throw NotImplementedException("Array models unimplemented.");
      } else if (k == UNINTERPRETED) {
        throw NotImplementedException("UF models unimplemented.");
      } else {
        std::string msg("Can't get value for term with kind = ");
        msg += to_string(k);
        throw IncorrectUsageException(msg.c_str());
      }
      return result;
    }
    Sort construct_sort(Kind k) const override
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
    Sort construct_sort(Kind k, unsigned int size) const override
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
    Sort construct_sort(Kind k, Sort idxsort, Sort elemsort) const override
    {
      if (k == ARRAY)
      {
        std::shared_ptr<BoolectorSortBase> btor_idxsort =
            std::static_pointer_cast<BoolectorSortBase>(idxsort);
        std::shared_ptr<BoolectorSortBase> btor_elemsort =
            std::static_pointer_cast<BoolectorSortBase>(elemsort);
        BoolectorSort bs = boolector_array_sort(btor, btor_idxsort->sort, btor_elemsort->sort);
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
    Sort construct_sort(Kind k, std::vector<Sort> sorts, Sort sort) const override
    {
      if (k == UNINTERPRETED)
        {
        int arity = sorts.size();
        std::vector<BoolectorSort> btor_sorts(arity);
        for (auto s : sorts) {
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
    Func construct_op(PrimOp prim_op, unsigned int idx) const override {
      IndexedOp io = std::make_shared<BoolectorSingleIndexOp>(prim_op, idx);
      Func f = io;
      return f;
    }
    Func construct_op(PrimOp prim_op, unsigned int idx0,
                    unsigned int idx1) const override {
      if (prim_op != BVEXTRACT) {
        std::string msg("Can't construct op from ");
        msg += to_string(prim_op);
        msg += " with two integer indices.";
        throw IncorrectUsageException(msg.c_str());
      }
      IndexedOp io = std::make_shared<BoolectorExtractOp>(prim_op, idx0, idx1);
      Func f(io);
      return f;
    }
    Term apply_func(PrimOp op, Term t) const override {
      try {
        std::shared_ptr<BoolectorTerm> bt =
            std::static_pointer_cast<BoolectorTerm>(t);
        BoolectorNode *result = unary_ops.at(op)(btor, bt->node);
        Term term(new BoolectorTerm(btor, result, std::vector<Term>{t}, op));
        return term;
      } catch (std::out_of_range o) {
        std::string msg("Can't apply ");
        msg += to_string(op);
        msg += " to a single term.";
        throw IncorrectUsageException(msg.c_str());
      }
    }
    Term apply_func(PrimOp op, Term t0, Term t1) const override {
      try {
        std::shared_ptr<BoolectorTerm> bt0 =
            std::static_pointer_cast<BoolectorTerm>(t0);
        std::shared_ptr<BoolectorTerm> bt1 =
            std::static_pointer_cast<BoolectorTerm>(t1);
        BoolectorNode *result = binary_ops.at(op)(btor, bt0->node, bt1->node);
        Term term(
            new BoolectorTerm(btor, result, std::vector<Term>{t0, t1}, op));
        return term;
      } catch (std::out_of_range o) {
        std::string msg("Can't apply ");
        msg += to_string(op);
        msg += " to a single term.";
        throw IncorrectUsageException(msg.c_str());
      }
    }
    Term apply_func(PrimOp op, Term t0, Term t1, Term t2) const override {
      try {
        std::shared_ptr<BoolectorTerm> bt0 =
            std::static_pointer_cast<BoolectorTerm>(t0);
        std::shared_ptr<BoolectorTerm> bt1 =
            std::static_pointer_cast<BoolectorTerm>(t1);
        std::shared_ptr<BoolectorTerm> bt2 =
            std::static_pointer_cast<BoolectorTerm>(t2);
        BoolectorNode *result =
            ternary_ops.at(op)(btor, bt0->node, bt1->node, bt2->node);
        Term term(
            new BoolectorTerm(btor, result, std::vector<Term>{t0, t1, t2}, op));
        return term;
      } catch (std::out_of_range o) {
        std::string msg("Can't apply ");
        msg += to_string(op);
        msg += " to a single term.";
        throw IncorrectUsageException(msg.c_str());
      }
    }
    Term apply_func(PrimOp op, std::vector<Term> terms) const override {
      unsigned int size = terms.size();
      // binary ops are most common, check this first
      if (size == 2) {
        return apply_func(op, terms[0], terms[1]);
      } else if (size == 1) {
        return apply_func(op, terms[0]);
      } else if (size == 3) {
        return apply_func(op, terms[0], terms[1], terms[2]);
      } else {
        std::string msg("There's no primitive op of arity ");
        msg += std::to_string(size);
        msg += ".";
        throw IncorrectUsageException(msg.c_str());
      }
    }
    Term apply_func(Func f, Term t) const override {
      if (std::holds_alternative<PrimOp>(f)) {
        return apply_func(std::get<PrimOp>(f), t);
      } else if (std::holds_alternative<IndexedOp>(f)) {
        std::shared_ptr<BoolectorIndexedOp> btor_io =
            std::static_pointer_cast<BoolectorIndexedOp>(
                std::get<IndexedOp>(f));
        if (btor_io->is_extract_op()) {
          std::shared_ptr<BoolectorTerm> bt =
              std::static_pointer_cast<BoolectorTerm>(t);
          BoolectorNode *slice = boolector_slice(
              btor, bt->node, btor_io->get_upper(), btor_io->get_lower());
          Term term(
              new BoolectorTerm(btor, slice, std::vector<Term>{t}, BVEXTRACT));
          return term;
        } else {
          // TODO: apply different indexed operations (repeat, zero_extend and
          // sign_extend)
          throw NotImplementedException("Not implemented yet.");
        }
      } else {
        // rely on the function application in the vector implementation
        return apply_func(f, std::vector<Term>{t});
      }
    }
    Term apply_func(Func f, Term t0, Term t1) const override {
      if (std::holds_alternative<PrimOp>(f)) {
        return apply_func(std::get<PrimOp>(f), t0, t1);
      } else if (std::holds_alternative<IndexedOp>(f)) {
        throw IncorrectUsageException(
            "No indexed operators that take two arguments");
      } else {
        // rely on the function application in the vector implementation
        return apply_func(f, std::vector<Term>{t0, t1});
      }
    }
    Term apply_func(Func f, Term t0, Term t1, Term t2) const override {
      if (std::holds_alternative<PrimOp>(f)) {
        return apply_func(std::get<PrimOp>(f), t0, t1, t2);
      } else if (std::holds_alternative<IndexedOp>(f)) {
        throw IncorrectUsageException(
            "No indexed operators that take three arguments");
      } else {
        // rely on the function application in the vector implementation
        return apply_func(f, std::vector<Term>{t0, t1, t2});
      }
    }
    Term apply_func(Func f, std::vector<Term> terms) const override {
      unsigned int size = terms.size();
      // Optimization: translate Op to PrimOp as early as possible to prevent
      // unpacking it multipe times
      if (std::holds_alternative<PrimOp>(f)) {
        return apply_func(std::get<PrimOp>(f), terms);
      } else if (size == 1) {
        return apply_func(f, terms[0]);
      } else if (size == 2) {
        return apply_func(f, terms[0], terms[1]);
      } else if (size == 3) {
        return apply_func(f, terms[0], terms[1], terms[2]);
      } else if (std::holds_alternative<UF>(f)) {
        std::shared_ptr<BoolectorUF> bf =
            std::static_pointer_cast<BoolectorUF>(std::get<UF>(f));
        std::vector<BoolectorNode *> args(size);
        std::shared_ptr<BoolectorTerm> bt;
        for (auto t : terms) {
          bt = std::static_pointer_cast<BoolectorTerm>(t);
          args.push_back(bt->node);
        }
        BoolectorNode *result = boolector_apply(btor, &args[0], size, bf->node);
        Term term(new BoolectorTerm(btor, result, terms, f));
      }

      // TODO: make this clearer -- might need to_string for generic op
      std::string msg("Can't find any matching ops to apply to ");
      msg += std::to_string(size);
      msg += " terms.";
      throw IncorrectUsageException(msg.c_str());
    }

  protected:
    Btor * btor;
  };
}

#endif
