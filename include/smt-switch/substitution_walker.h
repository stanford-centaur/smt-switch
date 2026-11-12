/*!
 * \file substitution_walker.h
 * \brief Substitution walker for doing substitutions with a persistent cache
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_SUBSTITUTION_WALKER_H
#define SMT_SWITCH_SUBSTITUTION_WALKER_H

#include "smt-switch/identity_walker.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/term.h"

namespace smt {
// class for doing substitutions
// can more efficient than SmtSolver::substitute if it
// is called repeatedly since it has a persistent cache
// NOTE: don't even need to override visit_term
//       just need to prepulate the cache
class SubstitutionWalker : public IdentityWalker
{
 public:
  SubstitutionWalker(const SmtSolver & solver, const UnorderedTermMap & smap);
  // defined in the .cpp to anchor the vtable
  ~SubstitutionWalker() override;
};
}  // namespace smt

#endif  // SMT_SWITCH_SUBSTITUTION_WALKER_H
