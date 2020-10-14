//#include "smt_defs.h"
//
//namespace smt {
//  class Z3SolverFactory
//  {
//  public:
//    static SmtSolver create();
//  };
//}  // namespace smt








#pragma once

#include "smt_defs.h"

namespace smt {
  class Z3SolverFactory
  {
  public:
    /** Create a Z3 SmtSolver
     *  @param logging if true creates a LoggingSolver wrapper
     *         around the solver that keeps a shadow DAG at
     *         the smt-switch level.
     *         For yices2, logging is *required* if you want
     *         to traverse terms.
     *  @return a Z3 SmtSolver
     */
    static SmtSolver create(bool logging);
  };
}  // namespace smt
