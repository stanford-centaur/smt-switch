/*********************                                                        */
/*! \file bitwuzla_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bitwuzla implementation of AbsSmtSolver
**
**
**/

#include "bitwuzla_solver.h"

#include "assert.h"

using namespace std;

namespace smt {

void BzlaSolver::set_opt(const string option, const string value)
{
  // TODO support more options
  if (option == "incremental")
  {
    bitwuzla_set_option(bzla, BITWUZLA_OPT_INCREMENTAL, (value == "true"));
  }
  else if (option == "produce-models")
  {
    bitwuzla_set_option(bzla, BITWUZLA_OPT_PRODUCE_MODELS, (value == "true"));
  }
  else
  {
    throw SmtException("Bitwuzla backend does not support option: " + option);
  }
}

void BzlaSolver::set_logic(const string logic)
{
  // no need to set logic in bitwuzla
  return;
}

void BzlaSolver::assert_formula(const Term & t)
{
  shared_ptr<BzlaTerm> bterm = static_pointer_cast<BzlaTerm>(t);
  bitwuzla_assert(bzla, bterm->term);
}

Result BzlaSolver::check_sat()
{
  BitwuzlaResult r = bitwuzla_check_sat(bzla);
  if (r == BITWUZLA_SAT)
  {
    return Result(SAT);
  }
  else if (r == BITWUZLA_UNSAT)
  {
    return Result(UNSAT);
  }
  else
  {
    assert(r == BITWUZLA_UNKNOWN);
    return Result(UNKNOWN);
  }
}

Result BzlaSolver::check_sat_assuming(const TermVec & assumptions)
{
  // TODO need to check they're all literals
  throw NotImplementedException("");
}

void BzlaSolver::push(uint64_t num) { bitwuzla_push(bzla, num); }

void BzlaSolver::pop(uint64_t num) { bitwuzla_pop(bzla, num); }

// TODO keep implementing methods starting with get_value

}  // namespace smt
