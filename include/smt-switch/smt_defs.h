/*!
 * \file smt_defs.h
 * \brief Pointers to the main abstract objects, with their containers and
 *        operators
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
#include <iosfwd>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace smt {

/* Sorts, terms, solvers */

class AbsSort;
using Sort = std::shared_ptr<AbsSort>;

class AbsTerm;
using Term = std::shared_ptr<AbsTerm>;

class AbsSmtSolver;
using SmtSolver = std::shared_ptr<AbsSmtSolver>;

class AbsSmtInterpolator;
using SmtInterpolator = std::shared_ptr<AbsSmtInterpolator>;

/* Datatypes */

class AbsDatatypeDecl;
using DatatypeDecl = std::shared_ptr<AbsDatatypeDecl>;

class AbsDatatypeConstructorDecl;
using DatatypeConstructorDecl = std::shared_ptr<AbsDatatypeConstructorDecl>;

class AbsDatatype;
using Datatype = std::shared_ptr<AbsDatatype>;

/* Shorthands for standard containers of the above types */

using SortVec = std::vector<Sort>;
using TermVec = std::vector<Term>;

using UnorderedSortSet = std::unordered_set<Sort>;
using UnorderedTermSet = std::unordered_set<Term>;

using UnorderedTermMap = std::unordered_map<Term, Term>;

/* Comparison operators (null pointer first) */

bool operator==(const Sort & s1, const Sort & s2);
bool operator!=(const Sort & s1, const Sort & s2);
bool operator<(const Sort & s1, const Sort & s2);
bool operator>(const Sort & s1, const Sort & s2);
bool operator<=(const Sort & s1, const Sort & s2);
bool operator>=(const Sort & s1, const Sort & s2);
std::ostream & operator<<(std::ostream & output, const Sort s);

bool operator==(const Term & t1, const Term & t2);
bool operator!=(const Term & t1, const Term & t2);
bool operator<(const Term & t1, const Term & t2);
bool operator>(const Term & t1, const Term & t2);
bool operator<=(const Term & t1, const Term & t2);
bool operator>=(const Term & t1, const Term & t2);
std::ostream & operator<<(std::ostream & output, const Term t);

bool operator==(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2);
bool operator!=(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2);
bool operator<(const DatatypeConstructorDecl & d1,
               const DatatypeConstructorDecl & d2);
bool operator>(const DatatypeConstructorDecl & d1,
               const DatatypeConstructorDecl & d2);
bool operator<=(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2);
bool operator>=(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2);

bool operator==(const Datatype & d1, const Datatype & d2);
bool operator!=(const Datatype & d1, const Datatype & d2);
bool operator<(const Datatype & d1, const Datatype & d2);
bool operator>(const Datatype & d1, const Datatype & d2);
bool operator<=(const Datatype & d1, const Datatype & d2);
bool operator>=(const Datatype & d1, const Datatype & d2);

}  // namespace smt

namespace std {
template <>
struct hash<smt::Sort>
{
  size_t operator()(const smt::Sort & s) const;
};

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
