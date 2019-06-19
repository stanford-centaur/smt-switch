#include "exceptions.h"

#include "cvc4_solver.h"

namespace smt {

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


}
