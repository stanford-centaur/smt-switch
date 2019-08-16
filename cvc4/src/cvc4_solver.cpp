#include "cvc4_solver.h"

namespace smt
{

/* CVC4Solver implementation */

void CVC4Solver::set_opt(const std::string option, bool value) const
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

void CVC4Solver::set_opt(const std::string option,
             const std::string value) const
{
  solver.setOption(option, value);
}

void CVC4Solver::set_logic(const std::string logic) const
{
  solver.setLogic(logic);
}

Term CVC4Solver::make_value(bool b) const
{
  Term c(new CVC4Term(solver.mkBoolean(b)));
  return c;
}

Term CVC4Solver::make_value(unsigned int i, Sort sort) const
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

Term CVC4Solver::make_value(std::string val, Sort sort) const
{
  SortKind sk = sort->get_sort_kind();
  ::CVC4::api::Term c;

  if ((sk == INT) || (sk == REAL))
  {
    c = solver.mkReal(val);
    }
    else if (sk == BV)
    {
      c = solver.mkBitVector(sort->get_width(), val, 10);
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

void CVC4Solver::assert_formula(const Term& t) const
{
  std::shared_ptr<CVC4Term> cterm = std::static_pointer_cast<CVC4Term>(t);
  solver.assertFormula(cterm->term);
}

Result CVC4Solver::check_sat() const
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

Term CVC4Solver::get_value(Term & t) const
{
  std::shared_ptr<CVC4Term> cterm = std::static_pointer_cast<CVC4Term>(t);
  Term val(new CVC4Term(solver.getValue(cterm->term)));
  return val;
}

Sort CVC4Solver::make_sort(const std::string name, unsigned int arity) const
{
  Sort s(new CVC4Sort(solver.declareSort(name, arity)));
  return s;
}

Sort CVC4Solver::make_sort(SortKind sk) const
{
  if (sk == INT)
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

Sort CVC4Solver::make_sort(SortKind sk, unsigned int size) const
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

Sort CVC4Solver::make_sort(SortKind sk, Sort idxsort, Sort elemsort) const
{
  if (sk == ARRAY)
  {
    std::shared_ptr<CVC4Sort> csort0 = std::static_pointer_cast<CVC4Sort>(idxsort);
    std::shared_ptr<CVC4Sort> csort1 = std::static_pointer_cast<CVC4Sort>(elemsort);
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

Sort CVC4Solver::make_sort(SortKind sk,
                           std::vector<Sort> sorts,
                           Sort sort) const
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

Term CVC4Solver::make_term(const std::string name, Sort sort) const
{
  std::shared_ptr<CVC4Sort> csort = std::static_pointer_cast<CVC4Sort>(sort);
  ::CVC4::api::Term t = solver.mkConst(csort->sort, name);
  Term res(new ::smt::CVC4Term(t));
  return res;
}

Term CVC4Solver::make_term(Op op, Term t) const
{
  std::shared_ptr<CVC4Term> cterm = std::static_pointer_cast<CVC4Term>(t);
  if (op.num_idx == 0)
  {
    Term result(new CVC4Term(solver.mkTerm(primop2kind.at(op.prim_op), cterm->term)));
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

Term CVC4Solver::make_term(Op op, Term t0, Term t1) const
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

Term CVC4Solver::make_term(Op op, Term t0, Term t1, Term t2) const
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

Term CVC4Solver::make_term(Op op, std::vector<Term> terms) const
{
  std::vector<::CVC4::api::Term> cterms;
  cterms.reserve(terms.size());
  std::shared_ptr<CVC4Term> cterm;
  for(auto t : terms)
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
