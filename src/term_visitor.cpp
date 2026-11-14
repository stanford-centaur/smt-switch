/*!
 * \file term_visitor.cpp
 * \brief Read-only term visitor class that can be inherited to inspect
 *        terms
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/term_visitor.h"

#include "smt-switch/smt_defs.h"
#include "smt-switch/term.h"

namespace smt {

void TermVisitor::visit(const Term & term)
{
  TermVec to_visit({ term });
  while (!to_visit.empty())
  {
    Term t = to_visit.back();
    to_visit.pop_back();
    if (!visited_.insert(t).second)
    {
      continue;
    }
    VisitResult res = visit_term(t);
    if (res == VisitResult::Abort)
    {
      return;
    }
    if (res == VisitResult::Continue)
    {
      for (const Term & c : t)
      {
        to_visit.push_back(c);
      }
    }
  }
}

}  // namespace smt
