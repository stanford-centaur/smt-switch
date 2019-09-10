#include "boolector_solver.h"

namespace smt {

/* Boolector op mappings */
// Boolector PrimOp mappings
typedef BoolectorNode * (*un_fun)(Btor *, BoolectorNode *);
typedef BoolectorNode * (*bin_fun)(Btor *, BoolectorNode *, BoolectorNode *);
typedef BoolectorNode * (*tern_fun)(Btor *,
                                    BoolectorNode *,
                                    BoolectorNode *,
                                    BoolectorNode *);

const std::unordered_map<PrimOp, un_fun> unary_ops({ { Not, boolector_not },
                                                     { BVNot, boolector_not },
                                                     { BVNeg,
                                                       boolector_neg } });

// Indexed Operators are implemented in boolector_solver.h in apply
const std::unordered_map<PrimOp, bin_fun> binary_ops(
    { { And, boolector_and },
      { Or, boolector_or },
      { Xor, boolector_xor },
      { Implies, boolector_implies },
      { Iff, boolector_iff },
      { Equal, boolector_eq },
      { Distinct, boolector_ne },
      { Concat, boolector_concat },
      // Indexed Op: Extract
      { BVAnd, boolector_and },
      { BVOr, boolector_or },
      { BVXor, boolector_xor },
      { BVNand, boolector_nand },
      { BVNor, boolector_nor },
      { BVXnor, boolector_xnor },
      { BVComp, boolector_eq },
      { BVAdd, boolector_add },
      { BVSub, boolector_sub },
      { BVMul, boolector_mul },
      { BVUdiv, boolector_udiv },
      { BVSdiv, boolector_sdiv },
      { BVUrem, boolector_urem },
      { BVSrem, boolector_srem },
      { BVSmod, boolector_smod },
      { BVShl, boolector_sll },
      { BVAshr, boolector_sra },
      { BVLshr, boolector_srl },
      { BVUlt, boolector_ult },
      { BVUle, boolector_ulte },
      { BVUgt, boolector_ugt },
      { BVUge, boolector_ugte },
      { BVSlt, boolector_slt },
      { BVSle, boolector_slte },
      { BVSgt, boolector_sgt },
      { BVSge, boolector_sgte },
      // Indexed Op: Zero_Extend
      // Indexed Op: Sign_Extend
      // Indexed Op: Repeat
      // Indexed Op: Rotate_Left
      // Indexed Op: Rotate_Right
      { Select, boolector_read } });

const std::unordered_map<PrimOp, tern_fun> ternary_ops(
    { { Ite, boolector_cond }, { Store, boolector_write } });

/* BoolectorSolver implementation */

void BoolectorSolver::set_opt(const std::string option, bool value) const
{
  // TODO: Implement this with a map
  if ((option == "produce-models") && value)
  {
    boolector_set_opt(btor, BTOR_OPT_MODEL_GEN, 1);
  }
  else if ((option == "incremental") && value)
  {
    boolector_set_opt(btor, BTOR_OPT_INCREMENTAL, 1);
  }
  else
  {
    std::string msg = "Option " + option;
    msg += " is not implemented for boolector.";
    throw NotImplementedException(msg.c_str());
  }
}

void BoolectorSolver::set_opt(const std::string option,
                              const std::string value) const
{
  throw NotImplementedException("String value for set_opt unimplemented");
}

void BoolectorSolver::set_logic(const std::string logic) const
{
  if ((logic != "QF_BV") & (logic != "QF_UFBV") & (logic != "QF_ABV")
      & (logic != "QF_AUFBV"))
  {
    throw IncorrectUsageException(
        "Boolector only supports logics using bit-vectors, arrays and "
        "uninterpreted functions");
  }
}

Term BoolectorSolver::make_value(bool b) const
{
  if (b)
  {
    Term term(new BoolectorTerm(
        btor, boolector_const(btor, "1"), std::vector<Term>{}, Op(), false));
    return term;
  }
  else
  {
    Term term(new BoolectorTerm(
        btor, boolector_const(btor, "0"), std::vector<Term>{}, Op(), false));
    return term;
  }
}

Term BoolectorSolver::make_value(unsigned int i, Sort sort) const
{
  std::shared_ptr<BoolectorSortBase> bs =
      std::static_pointer_cast<BoolectorSortBase>(sort);
  // note: give the constant value a null PrimOp
  Term term(new BoolectorTerm(btor,
                              boolector_int(btor, i, bs->sort),
                              std::vector<Term>{},
                              Op(),
                              false));
  return term;
}

Term BoolectorSolver::make_value(std::string val, Sort sort) const
{
  std::shared_ptr<BoolectorSortBase> bs =
    std::static_pointer_cast<BoolectorSortBase>(sort);
  Term term(new BoolectorTerm(btor,
                              boolector_constd(btor, bs->sort, val.c_str()),
                              std::vector<Term>{},
                              Op(),
                              false));
  return term;
}

void BoolectorSolver::assert_formula(const Term & t) const
{
  std::shared_ptr<BoolectorTerm> bt =
      std::static_pointer_cast<BoolectorTerm>(t);
  boolector_assert(btor, bt->node);
}

Result BoolectorSolver::check_sat() const
{
  if (boolector_sat(btor) == BOOLECTOR_SAT)
  {
    return Result(SAT);
  }
  else
  {
    return Result(UNSAT);
  }
};

Result BoolectorSolver::check_sat_assuming(const TermVec & assumptions) const
{
  std::shared_ptr<BoolectorTerm> bt;
  for (auto a : assumptions)
  {
    bt = std::static_pointer_cast<BoolectorTerm>(a);
    boolector_assume(btor, bt->node);
  }

  if (boolector_sat(btor) == BOOLECTOR_SAT)
  {
    return Result(SAT);
  }
  else
  {
    return Result(UNSAT);
  }
}

void BoolectorSolver::push(unsigned int num) const
{
  boolector_push(btor, num);
}

void BoolectorSolver::pop(unsigned int num) const { boolector_pop(btor, num); }

Term BoolectorSolver::get_value(Term & t) const
{
  Term result;
  std::shared_ptr<BoolectorTerm> bt =
      std::static_pointer_cast<BoolectorTerm>(t);
  SortKind sk = t->get_sort()->get_sort_kind();
  if ((sk == BV) || (sk == BOOL))
  {
    const char * assignment = boolector_bv_assignment(btor, bt->node);
    BoolectorNode * bc = boolector_const(btor, assignment);
    boolector_free_bv_assignment(btor, assignment);
    // note: give the constant value a null PrimOp
    result = std::make_shared<BoolectorTerm>(
        btor, bc, std::vector<Term>{}, NUM_OPS_AND_NULL, false);
  }
  else if (sk == ARRAY)
  {
    throw NotImplementedException("Array models unimplemented.");
  }
  else if (sk == FUNCTION)
  {
    throw NotImplementedException("UF models unimplemented.");
  }
  else
  {
    std::string msg("Can't get value for term with sort constructor = ");
    msg += to_string(sk);
    throw IncorrectUsageException(msg.c_str());
  }
  return result;
}

Sort BoolectorSolver::make_sort(const std::string name,
                                unsigned int arity) const
{
  throw IncorrectUsageException("Can't declare sorts with Boolector");
}

Sort BoolectorSolver::make_sort(SortKind sk) const
{
  if (sk == BOOL)
  {
    Sort s(new BoolectorBVSort(btor, boolector_bool_sort(btor), 1));
    return s;
  }
  else
  {
    std::string msg("Boolector does not support sort ");
    msg += to_string(sk);
    throw NotImplementedException(msg.c_str());
  }
}

Sort BoolectorSolver::make_sort(SortKind sk, unsigned int size) const
{
  if (sk == BV)
  {
    Sort s(new BoolectorBVSort(btor, boolector_bitvec_sort(btor, size), size));
    return s;
  }
  else
  {
    std::string msg("Can't create sort from sort constructor ");
    msg += to_string(sk);
    msg += " with int argument.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort BoolectorSolver::make_sort(SortKind sk, Sort idxsort, Sort elemsort) const
{
  if (sk == ARRAY)
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
    std::string msg("Can't create sort from sort constructor ");
    msg += to_string(sk);
    msg += " with two sort arguments.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort BoolectorSolver::make_sort(SortKind sk,
                                std::vector<Sort> sorts,
                                Sort sort) const
{
  if (sk == FUNCTION)
  {
    int arity = sorts.size();
    std::vector<BoolectorSort> btor_sorts;
    btor_sorts.reserve(arity);
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
    std::string msg("Can't create sort from sort constructor ");
    msg += to_string(sk);
    msg += " with a vector of sorts and a sort";
    throw IncorrectUsageException(msg.c_str());
  }
}

Term BoolectorSolver::make_term(const std::string name, Sort sort) const
{
  // TODO handle arrays correctly (need boolector_array instead of
  // boolector_var)
  std::shared_ptr<BoolectorSortBase> bs =
      std::static_pointer_cast<BoolectorSortBase>(sort);

  SortKind sk = sort->get_sort_kind();
  BoolectorNode * n;
  if (sk == ARRAY)
  {
    n = boolector_array(btor, bs->sort, name.c_str());
  }
  else if (sk == FUNCTION)
  {
    n = boolector_uf(btor, bs->sort, name.c_str());
  }
  else
  {
    n = boolector_var(btor, bs->sort, name.c_str());
  }

  // note: giving the symbol a null Op
  Term term(new BoolectorTerm(btor, n, std::vector<Term>{}, Op(), true));
  return term;
}

// Implementation of the AbsSmtSolver methods
Term BoolectorSolver::make_term(Op op, Term t) const
{
  if (op.num_idx == 0)
  {
    return apply_prim_op(op.prim_op, t);
  }
  else
  {
    std::shared_ptr<BoolectorTerm> bt =
        std::static_pointer_cast<BoolectorTerm>(t);
    Term term;
    BoolectorNode * btor_res;
    if (op.prim_op == Extract)
    {
      btor_res = boolector_slice(btor, bt->node, op.idx0, op.idx1);
    }
    else if (op.prim_op == Zero_Extend)
    {
      btor_res = boolector_uext(btor, bt->node, op.idx0);
    }
    else if (op.prim_op == Sign_Extend)
    {
      btor_res = boolector_sext(btor, bt->node, op.idx0);
    }
    else if (op.prim_op == Repeat)
    {
      btor_res = boolector_repeat(btor, bt->node, op.idx0);
    }
    else if (op.prim_op == Rotate_Left)
    {
      btor_res = custom_boolector_rotate_left(btor, bt->node, op.idx0);
    }
    else if (op.prim_op == Rotate_Right)
    {
      btor_res = custom_boolector_rotate_left(btor, bt->node, op.idx0);
    }
    else
    {
      std::string msg = "Could not find Boolector implementation of ";
      msg += to_string(op.prim_op);
      throw IncorrectUsageException(msg.c_str());
    }
    term = Term(
        new BoolectorTerm(btor, btor_res, std::vector<Term>{ t }, op, false));
    return term;
  }
}

Term BoolectorSolver::make_term(Op op, Term t0, Term t1) const
{
  if (op.num_idx == 0)
  {
    return apply_prim_op(op.prim_op, t0, t1);
  }
  else
  {
    throw IncorrectUsageException(
        "There are no supported indexed operators that take more than one "
        "argument");
  }
}

Term BoolectorSolver::make_term(Op op, Term t0, Term t1, Term t2) const
{
  if (op.num_idx == 0)
  {
    return apply_prim_op(op.prim_op, t0, t1, t2);
  }
  else
  {
    throw IncorrectUsageException(
        "There are no supported indexed operators that take more than one "
        "argument");
  }
}

Term BoolectorSolver::make_term(Op op, std::vector<Term> terms) const
{
  if (op.num_idx == 0)
  {
    return apply_prim_op(op.prim_op, terms);
  }
  else
  {
    if (terms.size() == 1)
    {
      return make_term(op, terms[0]);
    }
    else
    {
      throw IncorrectUsageException(
          "There are no supported indexed operators that take more than one "
          "argument");
    }
  }
}

Term BoolectorSolver::apply_prim_op(PrimOp op, Term t) const
{
  try
  {
    std::shared_ptr<BoolectorTerm> bt =
        std::static_pointer_cast<BoolectorTerm>(t);
    BoolectorNode * result = unary_ops.at(op)(btor, bt->node);
    Term term(
        new BoolectorTerm(btor, result, std::vector<Term>{ t }, op, false));
    return term;
  }
  catch (std::out_of_range & o)
  {
    std::string msg(to_string(op));
    msg += " unsupported or can't be applied to a single term.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Term BoolectorSolver::apply_prim_op(PrimOp op, Term t0, Term t1) const
{
  try
  {
    std::shared_ptr<BoolectorTerm> bt0 =
        std::static_pointer_cast<BoolectorTerm>(t0);
    std::shared_ptr<BoolectorTerm> bt1 =
        std::static_pointer_cast<BoolectorTerm>(t1);

    BoolectorNode * result;
    if (op == Apply)
    {
      std::shared_ptr<BoolectorTerm> bt =
          std::static_pointer_cast<BoolectorTerm>(t1);
      std::vector<BoolectorNode *> args = { bt->node };

      std::shared_ptr<BoolectorTerm> bt0 =
          std::static_pointer_cast<BoolectorTerm>(t0);
      result = boolector_apply(btor, &args[0], 1, bt0->node);
    }
    else
    {
      result = binary_ops.at(op)(btor, bt0->node, bt1->node);
    }
    Term term(new BoolectorTerm(
        btor, result, std::vector<Term>{ t0, t1 }, op, false));
    return term;
  }
  catch (std::out_of_range & o)
  {
    std::string msg(to_string(op));
    msg += " unsupported or can't be applied to two terms.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Term BoolectorSolver::apply_prim_op(PrimOp op, Term t0, Term t1, Term t2) const
{
  try
  {
    std::shared_ptr<BoolectorTerm> bt0 =
        std::static_pointer_cast<BoolectorTerm>(t0);
    std::shared_ptr<BoolectorTerm> bt1 =
        std::static_pointer_cast<BoolectorTerm>(t1);
    std::shared_ptr<BoolectorTerm> bt2 =
        std::static_pointer_cast<BoolectorTerm>(t2);
    BoolectorNode * result;
    if (op == Apply)
    {
      std::shared_ptr<BoolectorTerm> bt1 =
          std::static_pointer_cast<BoolectorTerm>(t1);
      std::shared_ptr<BoolectorTerm> bt2 =
          std::static_pointer_cast<BoolectorTerm>(t2);
      std::vector<BoolectorNode *> args = { bt1->node, bt2->node };

      std::shared_ptr<BoolectorTerm> bt0 =
          std::static_pointer_cast<BoolectorTerm>(t0);
      result = boolector_apply(btor, &args[0], 1, bt0->node);
    }
    else
    {
      result = ternary_ops.at(op)(btor, bt0->node, bt1->node, bt2->node);
    }

    Term term(new BoolectorTerm(
        btor, result, std::vector<Term>{ t0, t1, t2 }, op, false));
    return term;
  }
  catch (std::out_of_range & o)
  {
    std::string msg(to_string(op));
    msg += " unsupported or can't be applied to three terms.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Term BoolectorSolver::apply_prim_op(PrimOp op, std::vector<Term> terms) const
{
  unsigned int size = terms.size();
  // binary ops are most common, check this first
  if (size == 2)
  {
    return apply_prim_op(op, terms[0], terms[1]);
  }
  else if (size == 1)
  {
    return apply_prim_op(op, terms[0]);
  }
  else if (size == 3)
  {
    return apply_prim_op(op, terms[0], terms[1], terms[2]);
  }
  else
  {
    if (op == Apply)
    {
      std::vector<Term> termargs;
      termargs.reserve(size - 1);
      std::vector<BoolectorNode *> args;
      args.reserve(size - 1);
      std::shared_ptr<BoolectorTerm> bt;
      for (size_t i = 1; i < size; ++i)
      {
        bt = std::static_pointer_cast<BoolectorTerm>(terms[i]);
        args.push_back(bt->node);
        termargs.push_back(terms[i]);
      }
      std::shared_ptr<BoolectorTerm> bt0 =
          std::static_pointer_cast<BoolectorTerm>(terms[0]);
      BoolectorNode * result = boolector_apply(btor, &args[0], 1, bt0->node);

      Term term(new BoolectorTerm(btor, result, termargs, op, false));
      return term;
    }
    else
    {
      std::string msg(to_string(op));
      msg += " cannot be applied to ";
      msg += std::to_string(size);
      msg += " terms.";
      throw IncorrectUsageException(msg.c_str());
    }
  }
}

/* end BoolectorSolver implementation */

}  // namespace smt
