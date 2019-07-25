#include "boolector_solver.h"

namespace smt {

/* BoolectorSolver implementation */

void BoolectorSolver::set_opt(const std::string option, bool value) const
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

Sort BoolectorSolver::declare_sort(const std::string name,
                                   unsigned int arity) const
{
  throw IncorrectUsageException("Can't declare sorts with Boolector");
}

Term BoolectorSolver::declare_const(const std::string name, Sort sort) const
{
  // TODO handle arrays correctly (need boolector_array instead of
  // boolector_var)
  std::shared_ptr<BoolectorSortBase> bs =
      std::static_pointer_cast<BoolectorSortBase>(sort);

  BoolectorNode * n;
  if (sort->get_sort_con() != ARRAY)
  {
    n = boolector_var(btor, bs->sort, name.c_str());
  }
  else
  {
    n = boolector_array(btor, bs->sort, name.c_str());
  }

  // note: giving the symbol a null Op
  Term term(new BoolectorTerm(btor, n, std::vector<Term>{}, Op(), true));
  return term;
}

Fun BoolectorSolver::declare_fun(const std::string name,
                                 const std::vector<Sort> & sorts,
                                 Sort sort) const
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
    BoolectorNode * n = boolector_uf(btor, btor_fun_sort, name.c_str());
    // uf_sort owns btor_fun_sort
    Sort uf_sort(new BoolectorUFSort(btor, btor_fun_sort, sorts, sort));
    Fun f(new BoolectorFun(btor, n, uf_sort));
    return f;
  }
}

Term BoolectorSolver::make_const(bool b) const
{
  if (b)
  {
    Term term(new BoolectorTerm(
                                btor, boolector_const(btor, "1"), std::vector<Term>{}, Op(), false
    ));
    return term;
  }
  else
  {
    Term term(new BoolectorTerm(
                                btor, boolector_const(btor, "0"), std::vector<Term>{}, Op(), false
                                ));
    return term;
  }
}

Term BoolectorSolver::make_const(unsigned int i, Sort sort) const
{
  std::shared_ptr<BoolectorSortBase> bs =
      std::static_pointer_cast<BoolectorSortBase>(sort);
  // note: give the constant value a null PrimOp
  Term term(new BoolectorTerm(
                              btor, boolector_int(btor, i, bs->sort), std::vector<Term>{}, Op(), false));
  return term;
}

Term BoolectorSolver::make_const(std::string val, Sort sort) const
{
  std::shared_ptr<BoolectorSortBase> bs =
    std::static_pointer_cast<BoolectorSortBase>(sort);
  Term term(new BoolectorTerm(btor, boolector_constd(btor, bs->sort, val.c_str()), std::vector<Term>{}, Op(), false));
  return term;
}

Fun BoolectorSolver::make_fun(Op op) const
{
  Fun f(new BoolectorFun(op));
  return f;
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

Term BoolectorSolver::get_value(Term & t) const
{
  Term result;
  std::shared_ptr<BoolectorTerm> bt =
      std::static_pointer_cast<BoolectorTerm>(t);
  SortCon sc = t->get_sort()->get_sort_con();
  if ((sc == BV) || (sc == BOOL))
  {
    const char * assignment = boolector_bv_assignment(btor, bt->node);
    BoolectorNode * bc = boolector_const(btor, assignment);
    boolector_free_bv_assignment(btor, assignment);
    // note: give the constant value a null PrimOp
    result = std::make_shared<BoolectorTerm>(
                                             btor, bc, std::vector<Term>{}, NUM_OPS_AND_NULL, false);
  }
  else if (sc == ARRAY)
  {
    throw NotImplementedException("Array models unimplemented.");
  }
  else if (sc == UNINTERPRETED)
  {
    throw NotImplementedException("UF models unimplemented.");
  }
  else
  {
    std::string msg("Can't get value for term with sort constructor = ");
    msg += to_string(sc);
    throw IncorrectUsageException(msg.c_str());
  }
  return result;
}

Sort BoolectorSolver::make_sort(SortCon sc) const
{
  if (sc == BOOL)
  {
    Sort s(new BoolectorBVSort(btor, boolector_bool_sort(btor), 1));
    return s;
  }
  else
  {
    std::string msg("Boolector does not support sort ");
    msg += to_string(sc);
    throw NotImplementedException(msg.c_str());
  }
}

Sort BoolectorSolver::make_sort(SortCon sc, unsigned int size) const
{
  if (sc == BV)
  {
    Sort s(new BoolectorBVSort(btor, boolector_bitvec_sort(btor, size), size));
    return s;
  }
  else
  {
    std::string msg("Can't create sort from sort constructor ");
    msg += to_string(sc);
    msg += " with int argument.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort BoolectorSolver::make_sort(SortCon sc, Sort idxsort, Sort elemsort) const
{
  if (sc == ARRAY)
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
    msg += to_string(sc);
    msg += " with two sort arguments.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort BoolectorSolver::make_sort(SortCon sc,
                                std::vector<Sort> sorts,
                                Sort sort) const
{
  if (sc == UNINTERPRETED)
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
    std::string msg("Can't create sort from sort constructor ");
    msg += to_string(sc);
    msg += " with a vector of sorts and a sort";
    throw IncorrectUsageException(msg.c_str());
  }
}

Term BoolectorSolver::apply_prim_op(PrimOp op, Term t) const
{
  try
  {
    std::shared_ptr<BoolectorTerm> bt =
        std::static_pointer_cast<BoolectorTerm>(t);
    BoolectorNode * result = unary_ops.at(op)(btor, bt->node);
    Term term(new BoolectorTerm(btor, result, std::vector<Term>{ t }, op, false));
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
    BoolectorNode * result = binary_ops.at(op)(btor, bt0->node, bt1->node);
    Term term(new BoolectorTerm(btor, result, std::vector<Term>{ t0, t1 }, op, false));
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
    BoolectorNode * result =
        ternary_ops.at(op)(btor, bt0->node, bt1->node, bt2->node);
    Term term(
              new BoolectorTerm(btor, result, std::vector<Term>{ t0, t1, t2 }, op, false));
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
    std::string msg("There's no primitive op of arity ");
    msg += std::to_string(size);
    msg += ".";
    throw IncorrectUsageException(msg.c_str());
  }
}

// Implementation of the AbsSmtSolver methods
Term BoolectorSolver::apply(Op op, Term t) const
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
    term = Term(new BoolectorTerm(btor, btor_res, std::vector<Term>{ t }, op, false));
    return term;
  }
}

Term BoolectorSolver::apply(Op op, Term t0, Term t1) const
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

Term BoolectorSolver::apply(Op op, Term t0, Term t1, Term t2) const
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

Term BoolectorSolver::apply(Op op, std::vector<Term> terms) const
{
  if (op.num_idx == 0)
  {
    return apply_prim_op(op.prim_op, terms);
  }
  else
  {
    if (terms.size() == 1)
    {
      return apply(op, terms[0]);
    }
    else
    {
      throw IncorrectUsageException(
          "There are no supported indexed operators that take more than one "
          "argument");
    }
  }
}

Term BoolectorSolver::apply(Fun f, Term t) const
{
  if (f->is_op())
  {
    Op op = f->get_op();
    if (op.num_idx == 0)
    {
      return apply_prim_op(op.prim_op, t);
    }
    else
    {
      return apply(op, std::vector<Term>{ t });
    }
  }
  else
  {
    // rely on the function application in the vector implementation
    return apply(f, std::vector<Term>{ t });
  }
}

Term BoolectorSolver::apply(Fun f, Term t0, Term t1) const
{
  if (f->is_op())
  {
    Op op = f->get_op();
    if (op.num_idx == 0)
    {
      return apply_prim_op(op.prim_op, t0, t1);
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
    return apply(f, std::vector<Term>{ t0, t1 });
  }
}

Term BoolectorSolver::apply(Fun f, Term t0, Term t1, Term t2) const
{
  if (f->is_op())
  {
    Op op = f->get_op();
    if (op.num_idx == 0)
    {
      return apply_prim_op(op.prim_op, t0, t1, t2);
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
    return apply(f, std::vector<Term>{ t0, t1, t2 });
  }
}

Term BoolectorSolver::apply(Fun f, std::vector<Term> terms) const
{
  unsigned int size = terms.size();
  // Optimization: translate Op to PrimOp as early as possible to prevent
  // unpacking it multipe times
  if (f->is_op())
  {
    Op op = f->get_op();
    if (op.num_idx == 0)
    {
      return apply_prim_op(op.prim_op, terms);
    }
    else
    {
      return apply(op, terms);
    }
  }
  else if (f->is_uf())
  {
    std::shared_ptr<BoolectorFun> bf =
        std::static_pointer_cast<BoolectorFun>(f);
    std::vector<BoolectorNode *> args;
    std::shared_ptr<BoolectorTerm> bt;
    for (auto t : terms)
    {
      bt = std::static_pointer_cast<BoolectorTerm>(t);
      args.push_back(bt->node);
    }
    BoolectorNode * result = boolector_apply(btor, &args[0], size, bf->node);
    Term term(new BoolectorTerm(btor, result, terms, f, false));
    return term;
  }

  std::string msg("Can't find any matching ops to apply to ");
  msg += std::to_string(size);
  msg += " terms.";
  throw IncorrectUsageException(msg.c_str());
}

/* end BoolectorSolver implementation */

}  // namespace smt
