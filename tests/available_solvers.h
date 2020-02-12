#pragma once

#include <unordered_map>

#include "smt_defs.h"

namespace smt
{

typedef SmtSolver (*create_solver_fun)(void);

enum SolverEnum
{
 BTOR=0,
 CVC4,
 MSAT
};

typedef std::unordered_map<SolverEnum, create_solver_fun> CreateSolverFunsMap;

CreateSolverFunsMap available_solvers();

}
