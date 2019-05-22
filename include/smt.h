#ifndef SMT_H
#define SMT_H

#include <memory>

// Eventually we should guard these imports depending on which solvers are included
#include "boolector_uf.h"
#include "boolector_func.h"
#include "boolector_solver.h"
#include "boolector_sort.h"
#include "boolector_term.h"

namespace smt
{
  // Supported solvers -- when adding a new solver, create an enum for it here
  enum SmtSolverEnum
  {
   BOOLECTOR
  };

  SmtSolver create_solver(SmtSolverEnum se)
  {
    SmtSolver s;
    if (se == BOOLECTOR)
    {
      s = std::make_shared<BoolectorSolver>();
    }
    return s;
  }

}


#endif
