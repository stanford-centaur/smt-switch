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

#include "solver_utils.h"

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <string>

#include "exceptions.h"
#include "ops.h"
#include "solver.h"
#include "term.h"

namespace smt {

Term make_distinct(const AbsSmtSolver * solver, const TermVec & terms)
{
  assert(!terms.empty());

  TermVec pairs;
  for (std::size_t i = 0; i < terms.size(); ++i)
  {
    for (std::size_t j = 0; j < terms.size(); ++j)
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

std::uint32_t narrow_index(const Op & op, std::uint64_t idx)
{
  if (idx > std::numeric_limits<std::uint32_t>::max())
  {
    throw IncorrectUsageException("Index " + std::to_string(idx) + " of "
                                  + op.to_string()
                                  + " does not fit in the 32 bits this solver "
                                    "accepts");
  }
  return static_cast<std::uint32_t>(idx);
}

}  // namespace smt
