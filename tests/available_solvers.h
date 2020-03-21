#pragma once

#include <iostream>
#include <unordered_map>
#include <vector>

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

// Create a map from enums to available solver creation functions
CreateSolverFunsMap available_solvers();

// collect all the available solvers
std::vector<SolverEnum> available_solver_enums();

CreateSolverFunsMap available_interpolators();

std::vector<SolverEnum> available_interpolator_enums();

std::vector<SolverEnum> available_int_solver_enums();

std::ostream & operator<<(std::ostream & o, SolverEnum e);

}  // namespace smt_tests

// define hash for older compilers
namespace std {
// specialize template
template <>
struct hash<smt_tests::SolverEnum>
{
  size_t operator()(const smt_tests::SolverEnum se) const
  {
    return static_cast<size_t>(se);
  }
};
}  // namespace std
