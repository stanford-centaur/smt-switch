#include "cvc4_solver.h"

namespace smt
{

/* CVC4 Op mappings */
const std::unordered_map<PrimOp, ::CVC4::api::Kind> primop2kind({
    { And, ::CVC4::api::AND },
    { Or, ::CVC4::api::OR },
    { Xor, ::CVC4::api::XOR },
    { Not, ::CVC4::api::NOT },
    { Implies, ::CVC4::api::IMPLIES },
    { Ite, ::CVC4::api::ITE },
    { Iff, ::CVC4::api::EQUAL },
    { Equal, ::CVC4::api::EQUAL },
    { Distinct, ::CVC4::api::DISTINCT },
    /* Uninterpreted Functions */
    { Apply, ::CVC4::api::APPLY_UF },
    /* Arithmetic Theories */
    { Plus, ::CVC4::api::PLUS },
    { Minus, ::CVC4::api::MINUS },
    { Negate, ::CVC4::api::UMINUS },
    { Mult, ::CVC4::api::MULT },
    { Div, ::CVC4::api::DIVISION },
    { Lt, ::CVC4::api::LT },
    { Le, ::CVC4::api::LEQ },
    { Gt, ::CVC4::api::GT },
    { Ge, ::CVC4::api::GEQ },
    { Mod, ::CVC4::api::INTS_MODULUS },
    { Abs, ::CVC4::api::ABS },
    { Pow, ::CVC4::api::POW },
    { To_Real, ::CVC4::api::TO_REAL },
    { To_Int, ::CVC4::api::TO_INTEGER },
    { Is_Int, ::CVC4::api::IS_INTEGER },
    /* Fixed Size BitVector Theory */
    { Concat, ::CVC4::api::BITVECTOR_CONCAT },
    // Indexed Op
    { Extract, ::CVC4::api::BITVECTOR_EXTRACT },
    { BVNot, ::CVC4::api::BITVECTOR_NOT },
    { BVNeg, ::CVC4::api::BITVECTOR_NEG },
    { BVAnd, ::CVC4::api::BITVECTOR_AND },
    { BVOr, ::CVC4::api::BITVECTOR_OR },
    { BVXor, ::CVC4::api::BITVECTOR_XOR },
    { BVNand, ::CVC4::api::BITVECTOR_NAND },
    { BVNor, ::CVC4::api::BITVECTOR_NOR },
    { BVXnor, ::CVC4::api::BITVECTOR_XNOR },
    { BVComp, ::CVC4::api::BITVECTOR_COMP },
    { BVAdd, ::CVC4::api::BITVECTOR_PLUS },
    { BVSub, ::CVC4::api::BITVECTOR_SUB },
    { BVMul, ::CVC4::api::BITVECTOR_MULT },
    { BVUdiv, ::CVC4::api::BITVECTOR_UDIV },
    { BVSdiv, ::CVC4::api::BITVECTOR_SDIV },
    { BVUrem, ::CVC4::api::BITVECTOR_UREM },
    { BVSrem, ::CVC4::api::BITVECTOR_SREM },
    { BVSmod, ::CVC4::api::BITVECTOR_SMOD },
    { BVShl, ::CVC4::api::BITVECTOR_SHL },
    { BVAshr, ::CVC4::api::BITVECTOR_ASHR },
    { BVLshr, ::CVC4::api::BITVECTOR_LSHR },
    { BVUlt, ::CVC4::api::BITVECTOR_ULT },
    { BVUle, ::CVC4::api::BITVECTOR_ULE },
    { BVUgt, ::CVC4::api::BITVECTOR_UGT },
    { BVUge, ::CVC4::api::BITVECTOR_UGE },
    { BVSlt, ::CVC4::api::BITVECTOR_SLT },
    { BVSle, ::CVC4::api::BITVECTOR_SLE },
    { BVSgt, ::CVC4::api::BITVECTOR_SGT },
    { BVSge, ::CVC4::api::BITVECTOR_SGE },
    // Indexed Op
    { Zero_Extend, ::CVC4::api::BITVECTOR_ZERO_EXTEND },
    // Indexed Op
    { Sign_Extend, ::CVC4::api::BITVECTOR_SIGN_EXTEND },
    // Indexed Op
    { Repeat, ::CVC4::api::BITVECTOR_REPEAT },
    // Indexed Op
    { Rotate_Left, ::CVC4::api::BITVECTOR_ROTATE_LEFT },
    // Indexed Op
    { Rotate_Right, ::CVC4::api::BITVECTOR_ROTATE_RIGHT },
    { Select, ::CVC4::api::SELECT },
    { Store, ::CVC4::api::STORE },
});

const std::unordered_map<::CVC4::api::Kind, PrimOp> kind2primop(
    { { ::CVC4::api::AND, And },
      { ::CVC4::api::OR, Or },
      { ::CVC4::api::XOR, Xor },
      { ::CVC4::api::NOT, Not },
      { ::CVC4::api::IMPLIES, Implies },
      { ::CVC4::api::ITE, Ite },
      { ::CVC4::api::EQUAL, Iff },
      { ::CVC4::api::EQUAL, Equal },
      { ::CVC4::api::DISTINCT, Distinct },
      { ::CVC4::api::BITVECTOR_CONCAT, Concat },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_EXTRACT, Extract },
      { ::CVC4::api::BITVECTOR_NOT, BVNot },
      { ::CVC4::api::BITVECTOR_NEG, BVNeg },
      { ::CVC4::api::BITVECTOR_AND, BVAnd },
      { ::CVC4::api::BITVECTOR_OR, BVOr },
      { ::CVC4::api::BITVECTOR_XOR, BVXor },
      { ::CVC4::api::BITVECTOR_NAND, BVNand },
      { ::CVC4::api::BITVECTOR_NOR, BVNor },
      { ::CVC4::api::BITVECTOR_XNOR, BVXnor },
      { ::CVC4::api::BITVECTOR_COMP, BVComp },
      { ::CVC4::api::BITVECTOR_PLUS, BVAdd },
      { ::CVC4::api::BITVECTOR_SUB, BVSub },
      { ::CVC4::api::BITVECTOR_MULT, BVMul },
      { ::CVC4::api::BITVECTOR_UDIV, BVUdiv },
      { ::CVC4::api::BITVECTOR_SDIV, BVSdiv },
      { ::CVC4::api::BITVECTOR_UREM, BVUrem },
      { ::CVC4::api::BITVECTOR_SREM, BVSrem },
      { ::CVC4::api::BITVECTOR_SMOD, BVSmod },
      { ::CVC4::api::BITVECTOR_SHL, BVShl },
      { ::CVC4::api::BITVECTOR_ASHR, BVAshr },
      { ::CVC4::api::BITVECTOR_LSHR, BVLshr },
      { ::CVC4::api::BITVECTOR_ULT, BVUlt },
      { ::CVC4::api::BITVECTOR_ULE, BVUle },
      { ::CVC4::api::BITVECTOR_UGT, BVUgt },
      { ::CVC4::api::BITVECTOR_UGE, BVUge },
      { ::CVC4::api::BITVECTOR_SLT, BVSlt },
      { ::CVC4::api::BITVECTOR_SLE, BVSle },
      { ::CVC4::api::BITVECTOR_SGT, BVSgt },
      { ::CVC4::api::BITVECTOR_SGE, BVSge },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_ZERO_EXTEND, Zero_Extend },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_SIGN_EXTEND, Sign_Extend },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_REPEAT, Repeat },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_ROTATE_LEFT, Rotate_Left },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_ROTATE_RIGHT, Rotate_Right },
      { ::CVC4::api::SELECT, Select },
      { ::CVC4::api::STORE, Store } });

// the kinds CVC4 needs to build an OpTerm for an indexed op
const std::unordered_map<PrimOp, ::CVC4::api::Kind> primop2optermcon({
    { Extract, ::CVC4::api::BITVECTOR_EXTRACT_OP },
    { Zero_Extend, ::CVC4::api::BITVECTOR_ZERO_EXTEND_OP },
    { Sign_Extend, ::CVC4::api::BITVECTOR_SIGN_EXTEND_OP },
    { Repeat, ::CVC4::api::BITVECTOR_REPEAT_OP },
    { Rotate_Left, ::CVC4::api::BITVECTOR_ROTATE_LEFT_OP },
    { Rotate_Right, ::CVC4::api::BITVECTOR_ROTATE_RIGHT_OP },
});

/* CVC4Solver implementation */

void CVC4Solver::set_opt(const std::string option, bool value) const
{
  try
  {
    if (value)
    {
      solver.setOption(option, "true");
    }
    else
    {
      solver.setOption(option, "false");
    }
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::set_opt(const std::string option,
             const std::string value) const
{
  try
  {
    solver.setOption(option, value);
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::set_logic(const std::string logic) const
{
  try
  {
    solver.setLogic(logic);
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_value(bool b) const
{
  try
  {
    Term c(new CVC4Term(solver.mkBoolean(b)));
    return c;
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_value(unsigned int i, Sort sort) const
{
  try
  {
    SortKind sk = sort->get_sort_kind();
    ::CVC4::api::Term c;

    if ((sk == INT) || (sk == REAL))
    {
      c = solver.mkReal(i);
    }
    else if (sk == BV)
    {
      c = solver.mkBitVector(sort->get_width(), i);
    }
    else
    {
      std::string msg = "Can't create constant with integer for sort ";
      msg += sort->to_string();
      throw IncorrectUsageException(msg.c_str());
    }

    Term res(new CVC4Term(c));
    return res;
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_value(std::string val, Sort sort, unsigned int base) const
{
  try
  {
    SortKind sk = sort->get_sort_kind();
    ::CVC4::api::Term c;

    if ((sk == INT) || (sk == REAL))
    {
      // TODO: Only do these checks in debug
      if (base != 10)
      {
        throw IncorrectUsageException("Can't use non-decimal base for reals and ints");
      }
      c = solver.mkReal(val);
    }
    else if (sk == BV)
    {
      c = solver.mkBitVector(sort->get_width(), val, base);
    }
    else
    {
      std::string msg = "Can't create constant with integer for sort ";
      msg += sort->to_string();
      throw IncorrectUsageException(msg.c_str());
    }

    Term res(new CVC4Term(c));
    return res;
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::assert_formula(const Term& t) const
{
  try
  {
    std::shared_ptr<CVC4Term> cterm = std::static_pointer_cast<CVC4Term>(t);
    solver.assertFormula(cterm->term);
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Result CVC4Solver::check_sat() const
{
  try
  {
    ::CVC4::api::Result r = solver.checkSat();
    if (r.isUnsat())
    {
      return Result(UNSAT);
    }
    else if (r.isSat())
    {
      return Result(SAT);
    }
    else if (r.isSatUnknown())
    {
      return Result(UNKNOWN, r.getUnknownExplanation());
    }
    else
    {
      throw NotImplementedException("Unimplemented result type from CVC4");
    }
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Result CVC4Solver::check_sat_assuming(const TermVec & assumptions) const
{
  try
  {
    std::vector<::CVC4::api::Term> cvc4assumps;
    cvc4assumps.reserve(assumptions.size());

    std::shared_ptr<CVC4Term> cterm;
    for (auto a : assumptions)
    {
      cvc4assumps.push_back(std::static_pointer_cast<CVC4Term>(a)->term);
    }
    ::CVC4::api::Result r = solver.checkSatAssuming(cvc4assumps);
    if (r.isUnsat())
    {
      return Result(UNSAT);
    }
    else if (r.isSat())
    {
      return Result(SAT);
    }
    else if (r.isSatUnknown())
    {
      return Result(UNKNOWN, r.getUnknownExplanation());
    }
    else
    {
      throw NotImplementedException("Unimplemented result type from CVC4");
    }
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::push(unsigned int num) const
{
  try
  {
    solver.push(num);
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::pop(unsigned int num) const
{
  try
  {
    solver.pop(num);
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::get_value(Term & t) const
{
  try
  {
    std::shared_ptr<CVC4Term> cterm = std::static_pointer_cast<CVC4Term>(t);
    Term val(new CVC4Term(solver.getValue(cterm->term)));
    return val;
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort CVC4Solver::make_sort(const std::string name, unsigned int arity) const
{
  try
  {
    Sort s(new CVC4Sort(solver.declareSort(name, arity)));
    return s;
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort CVC4Solver::make_sort(SortKind sk) const
{
  try
  {
    if (sk == BOOL)
    {
      Sort s(new CVC4Sort(solver.getBooleanSort()));
      return s;
    }
    else if (sk == INT)
    {
      Sort s(new CVC4Sort(solver.getIntegerSort()));
      return s;
    }
    else if (sk == REAL)
    {
      Sort s(new CVC4Sort(solver.getRealSort()));
      return s;
    }
    else
    {
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and no arguments";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort CVC4Solver::make_sort(SortKind sk, unsigned int size) const
{
  try
  {
    if (sk == BV)
    {
      Sort s(new CVC4Sort(solver.mkBitVectorSort(size)));
      return s;
    }
    else
    {
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and an integer argument";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort CVC4Solver::make_sort(SortKind sk, Sort idxsort, Sort elemsort) const
{
  try
  {
    if (sk == ARRAY)
    {
      std::shared_ptr<CVC4Sort> csort0 =
          std::static_pointer_cast<CVC4Sort>(idxsort);
      std::shared_ptr<CVC4Sort> csort1 =
          std::static_pointer_cast<CVC4Sort>(elemsort);
      Sort s(new CVC4Sort(solver.mkArraySort(csort0->sort, csort1->sort)));
      return s;
    }
    else
    {
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and two Sort arguments";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort CVC4Solver::make_sort(SortKind sk,
                           std::vector<Sort> sorts,
                           Sort sort) const
{
  try
  {
    if (sorts.size() == 0)
    {
      return make_sort(sort->get_sort_kind());
    }

    std::vector<::CVC4::api::Sort> csorts;
    csorts.reserve(sorts.size());
    ::CVC4::api::Sort csort;
    for (Sort s : sorts)
    {
      csort = std::static_pointer_cast<CVC4Sort>(s)->sort;
      csorts.push_back(csort);
    }
    csort = std::static_pointer_cast<CVC4Sort>(sort)->sort;
    ::CVC4::api::Sort cfunsort = solver.mkFunctionSort(csorts, csort);
    Sort funsort(new CVC4Sort(cfunsort));
    return funsort;
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_term(const std::string name, Sort sort)
{
  // check that name is available
  // to make CVC4 behave the same as other solvers
  if (symbols.find(name) != symbols.end())
  {
    throw IncorrectUsageException("symbol " + name + " has already been used.");
  }

  try
  {
    std::shared_ptr<CVC4Sort> csort = std::static_pointer_cast<CVC4Sort>(sort);
    ::CVC4::api::Term t = solver.mkConst(csort->sort, name);
    Term res(new ::smt::CVC4Term(t));
    symbols[name] = res;
    return res;
  }
  catch(std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_term(Op op, Term t) const
{
  try
  {
    std::shared_ptr<CVC4Term> cterm = std::static_pointer_cast<CVC4Term>(t);
    if (op.num_idx == 0)
    {
      Term result(
          new CVC4Term(solver.mkTerm(primop2kind.at(op.prim_op), cterm->term)));
      return result;
    }
    else
    {
      ::CVC4::api::OpTerm ot = make_op_term(op);
      Term result(new CVC4Term(
          solver.mkTerm(primop2kind.at(op.prim_op), ot, cterm->term)));
      return result;
    }
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_term(Op op, Term t0, Term t1) const
{
  try
  {
    std::shared_ptr<CVC4Term> cterm0 = std::static_pointer_cast<CVC4Term>(t0);
    std::shared_ptr<CVC4Term> cterm1 = std::static_pointer_cast<CVC4Term>(t1);
    if (op.num_idx == 0)
    {
      Term result(new CVC4Term(solver.mkTerm(primop2kind.at(op.prim_op),
                                             cterm0->term,
                                             cterm1->term)));
      return result;
    }
  else
    {
      ::CVC4::api::OpTerm ot = make_op_term(op);
      Term result(new CVC4Term(solver.mkTerm(
          primop2kind.at(op.prim_op), ot, cterm0->term, cterm1->term)));
      return result;
    }
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_term(Op op, Term t0, Term t1, Term t2) const
{
  try
  {
    std::shared_ptr<CVC4Term> cterm0 = std::static_pointer_cast<CVC4Term>(t0);
    std::shared_ptr<CVC4Term> cterm1 = std::static_pointer_cast<CVC4Term>(t1);
    std::shared_ptr<CVC4Term> cterm2 = std::static_pointer_cast<CVC4Term>(t2);
    if (op.num_idx == 0)
    {
      Term result(new CVC4Term(solver.mkTerm(primop2kind.at(op.prim_op),
                                             cterm0->term,
                                             cterm1->term,
                                             cterm2->term)));
      return result;
    }
  else
    {
      ::CVC4::api::OpTerm ot = make_op_term(op);
      Term result(new CVC4Term(solver.mkTerm(primop2kind.at(op.prim_op),
                                             ot,
                                             cterm0->term,
                                             cterm1->term,
                                             cterm2->term)));
      return result;
    }
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_term(Op op, std::vector<Term> terms) const
{
  try
  {
    std::vector<::CVC4::api::Term> cterms;
    cterms.reserve(terms.size());
    std::shared_ptr<CVC4Term> cterm;
    for (auto t : terms)
    {
      cterm = std::static_pointer_cast<CVC4Term>(t);
      cterms.push_back(cterm->term);
    }
    if (op.num_idx == 0)
    {
      Term result(
          new CVC4Term(solver.mkTerm(primop2kind.at(op.prim_op), cterms)));
      return result;
    }
    else
    {
      ::CVC4::api::OpTerm ot = make_op_term(op);
      Term result(
          new CVC4Term(solver.mkTerm(primop2kind.at(op.prim_op), ot, cterms)));
      return result;
    }
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::reset()
{
  try
  {
    solver.reset();
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::reset_assertions()
{
  try
  {
    solver.resetAssertions();
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

bool CVC4Solver::has_symbol(const std::string name) const
{
  return (symbols.find(name) != symbols.end());
}

Term CVC4Solver::lookup_symbol(const std::string name) const
{
  try
  {
    return symbols.at(name);
  }
  catch(std::exception & e)
  {
    throw IncorrectUsageException("Cannot lookup unknown symbol: " + name);
  }

}


/**
   Helper function for creating an OpTerm from an Op
   Preconditions: op must be indexed, i.e. op.num_idx > 0
*/
::CVC4::api::OpTerm CVC4Solver::make_op_term(Op op) const
{
  if (op.num_idx == 1)
  {
    return solver.mkOpTerm(primop2optermcon.at(op.prim_op), op.idx0);
  }
  else if (op.num_idx == 2)
  {
    return solver.mkOpTerm(primop2optermcon.at(op.prim_op), op.idx0, op.idx1);
  }
  else
  {
    throw NotImplementedException(
        "CVC4 does not have any indexed "
        "operators with more than two indices");
  }
}

/* end CVC4Solver implementation */

}
