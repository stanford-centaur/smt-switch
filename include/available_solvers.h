#pragma once

#include <unordered_map>

#include "smt_defs.h"

namespace smt
{

typedef SmtSolver (*create_solver_fun)();

enum SolverEnum
{
 BTOR=0,
 CVC4,
 MSAT
};

typedef std::unordered_map<SolverEnum, create_solver_fun> SolverMap;

const SolverMap available_solvers();

}
