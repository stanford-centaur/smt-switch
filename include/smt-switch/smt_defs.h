/*!
 * \file smt_defs.h
 * \brief Type definitions for pointers to main abstract objects
 * \author Clark Barrett
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_SMT_DEFS_H
#define SMT_SWITCH_SMT_DEFS_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <cstddef>
#include <memory>

namespace smt {

struct Op;

class AbsSort;
using Sort = std::shared_ptr<AbsSort>;

class AbsTerm;
using Term = std::shared_ptr<AbsTerm>;

class AbsSmtSolver;
using SmtSolver = std::shared_ptr<AbsSmtSolver>;

class AbsSmtInterpolator;
using SmtInterpolator = std::shared_ptr<AbsSmtInterpolator>;

// Datatype theory related
class AbsDatatypeDecl;
using DatatypeDecl = std::shared_ptr<AbsDatatypeDecl>;

class AbsDatatypeConstructorDecl;
using DatatypeConstructorDecl = std::shared_ptr<AbsDatatypeConstructorDecl>;

class AbsDatatype;
using Datatype = std::shared_ptr<AbsDatatype>;

}  // namespace smt

namespace std {
template <>
struct hash<smt::Term>
{
  size_t operator()(const smt::Term & t) const;
};

template <>
struct hash<smt::DatatypeConstructorDecl>
{
  size_t operator()(const smt::DatatypeConstructorDecl & d) const;
};

template <>
struct hash<smt::Datatype>
{
  size_t operator()(const smt::Datatype & d) const;
};
}  // namespace std

#endif  // SMT_SWITCH_SMT_DEFS_H
