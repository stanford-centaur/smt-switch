/*********************                                                        */
/*! \file test-utils.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Convenience functions for testing.
**
**
**/

#include "test-utils.h"

using namespace std;
using namespace smt;

namespace smt_tests {

UnorderedTermSet get_free_symbols(Term & t)
{
  UnorderedTermSet free_symbols;
  TermVec to_visit({ t });
  UnorderedTermSet visited;

  Term n;
  while (to_visit.size())
  {
    n = to_visit.back();
    to_visit.pop_back();

    if (visited.find(n) == visited.end())
    {
      visited.insert(n);
      for (auto nn : n)
      {
        to_visit.push_back(nn);
      }

      if (n->is_symbolic_const())
      {
        free_symbols.insert(n);
      }
    }
  }

  return free_symbols;
}

}  // namespace smt_tests
