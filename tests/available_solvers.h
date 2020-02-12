#pragma once

#include <iostream>
#include <unordered_map>

#include "smt_defs.h"

namespace smt_tests {

typedef ::smt::SmtSolver (*create_solver_fun)(void);

enum SolverEnum
{
  BTOR = 0,
  CVC4,
  MSAT
};

typedef std::unordered_map<SolverEnum, create_solver_fun> CreateSolverFunsMap;

CreateSolverFunsMap available_solvers();

std::ostream & operator<<(std::ostream & o, SolverEnum e);

}  // namespace smt_tests
