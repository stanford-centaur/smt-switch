/*********************                                                        */
/*! \file solver_utils.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions for solver implementations. Meant for internal
**        use only, not from the API.
**
**/

#include "assert.h"

#include "solver_utils.h"

namespace smt {

Term make_distinct(const AbsSmtSolver * solver, const TermVec & terms)
{
  size_t size = terms.size();
  assert(size);

  TermVec pairs;
  for (size_t i = 0; i < terms.size(); ++i)
  {
    for (size_t j = 0; j < terms.size(); ++j)
    {
      if (i != j)
      {
        // trivially false if same term shows up twice
        assert(terms[i] != terms[j]);
        pairs.push_back(solver->make_term(Distinct, terms[i], terms[j]));
      }
    }
  }

  Term res = solver->make_term(And, pairs);
  return res;
}

}  // namespace smt
