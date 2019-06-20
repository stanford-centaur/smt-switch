#include "exceptions.h"

#include "cvc4_solver.h"

namespace smt {

CVC4Solver::CVC4Solver()
{
  // require the solver to use smt-lib format
  solver.setOption("lang", "smt2");
}

void CVC4Solver::set_opt(const std::string option, bool value) const
{
  if (value)
    {
      solver.setOption(option, "true");
    }
  else {
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

Sort CVC4Solver::declare_sort(const std::string name,
                  unsigned int arity) const
{
  Sort s(new CVC4Sort(solver.declareSort(name, arity)));
  return s
    }

Term CVC4Solver::declare_const(const std::string name, Sort sort) const
{
  CVC4Sort csort = *std::static_pointer<CVC4Sort>(sort);
  ::CVC4::api::Term t = solver.mkVar(csort.sort, name);
  Term t(new CVC4Term(t));
  return t;
}

Fun CVC4Solver::declare_fun(const std::string name,
                const std::vector<Sort>& sorts,
                Sort sort) const
{
  std::vector<::CVC4::api::Sort> csorts;
  csorts.reserve(sorts.size());
  ::CVC4::api::Sort csort;
  for (Sort s : sorts)
    {
      csort = *std::static_pointer_cast<CVC4Sort>(s);
      csorts.push_back(csort);
    }
  csort = *std::static_pointer_cast<CVC4Sort>(sort);
  ::CVC4::api::Term fun = solver.declareFun(name, csorts, csort);
  Fun f(new CVC4Fun(fun));
  return f;
}

Term CVC4Solver::make_const(std::string val, Sort sort) const
{
  std::shared_ptr<CVC4Sort> csort = std::static_pointer_cast<CVC4Sort>(sort);
  Term t(new CVC4Term(solver.mkConst(csort->sort, val)));
  return t;
}

Fun CVC4Solver::make_fun(Op op)
{
  Fun f;
  if (op.num_idx == 0)
  {
    Fun f(new CVC4Fun(primop2kind[op.prim_op]));
    return f;
  }
  else if (op.num_idx == 1)
  {
    ::CVC4::api::OpTerm ot = solver.mkOpTerm(primop2kind[op.prim_op], op.idx0);
    Fun f(new CVC4Fun(ot));
    return f;
  }
  else
  {
    ::CVC4::api::OpTerm ot = solver.mkOpTerm(primop2kind[op.prim_op], op.idx0, op.idx1);
    Fun f(new CVC4Fun(ot));
    return f;
  }
}

void CVC4Solver::assert_formula(const Term& t) const
{
  std::shared_ptr<CVC4Term> cterm = std::static_pointer_cast<CVC4Term>(t);
  solver.assertFormula(cterm->term);
}

Result CVC4Solver::check_sat() const
{
  ::CVC4::api::Result r = solver.check_sat();
  if (r.isUnsat())
  {
    return Result(UNSAT);
  }
  else if (r.isSat())
  {
    return Result(SAT);
  }
  else if (r.isUnknown())
  {
    return Result(UNKNOWN, r.getUnknownExplanation());
  }
  else
  {
    throw NotImplementedException("Unimplemented result type from CVC4");
  }
}

}
