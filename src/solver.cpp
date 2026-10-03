/*********************                                                        */
/*! \file solver.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Abstract interface for SMT solvers.
**
**
**/

#include "solver.h"

#include <cassert>
#include <cstddef>

#include "exceptions.h"
#include "result.h"
#include "smt_defs.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

namespace smt {

// TODO: Implement a generic visitor

Result AbsSmtSolver::check_sat_assuming_list(const TermList & assumptions)
{
  return check_sat_assuming(assumptions);
}

Result AbsSmtSolver::check_sat_assuming_set(
    const UnorderedTermSet & assumptions)
{
  return check_sat_assuming(assumptions);
}

Sort AbsSmtSolver::make_sort(const Sort & /* sort_con */,
                             const SortVec & /* sorts */) const
{
  throw NotImplementedException(
      "Uninterpreted sort constructors are not supported by "
      + to_string(solver_enum));
}

Term AbsSmtSolver::make_term(const std::string & /* s */,
                             bool /* useEscSequences */,
                             const Sort & /* sort */) const
{
  throw NotImplementedException("Strings are not supported by "
                                + to_string(solver_enum));
}

Term AbsSmtSolver::make_term(const std::wstring & /* s */,
                             const Sort & /* sort */) const
{
  throw NotImplementedException("Strings are not supported by "
                                + to_string(solver_enum));
}

Sort AbsSmtSolver::make_sort(const DatatypeDecl & /* d */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

DatatypeDecl AbsSmtSolver::make_datatype_decl(const std::string & /* s */)
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

DatatypeConstructorDecl AbsSmtSolver::make_datatype_constructor_decl(
    const std::string /* s */)
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

void AbsSmtSolver::add_constructor(
    DatatypeDecl & /* dt */, const DatatypeConstructorDecl & /* con */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

void AbsSmtSolver::add_selector(DatatypeConstructorDecl & /* dt */,
                                const std::string & /* name */,
                                const Sort & /* s */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

void AbsSmtSolver::add_selector_self(DatatypeConstructorDecl & /* dt */,
                                     const std::string & /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

Term AbsSmtSolver::get_constructor(const Sort & /* s */,
                                   std::string /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

Term AbsSmtSolver::get_tester(const Sort & /* s */,
                              std::string /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

Term AbsSmtSolver::get_selector(const Sort & /* s */,
                                std::string /* con */,
                                std::string /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

SortVec AbsSmtSolver::make_datatype_sorts(
    const std::vector<DatatypeDecl> & decls) const
{
  throw NotImplementedException(
      "make_datatype_sorts for mutually recursive datatypes not yet "
      "implemented by "
      + to_string(solver_enum));
}

Sort AbsSmtSolver::make_datatype_sort(const DatatypeDecl & decl) const
{
  SortVec datatype_sorts = make_datatype_sorts({ decl });
  assert(datatype_sorts.size() == 1);
  return datatype_sorts[0];
}

Term AbsSmtSolver::substitute(const Term term,
                              const UnorderedTermMap & substitution_map) const
{
  // cache starts with the substitutions
  UnorderedTermMap cache(substitution_map);
  TermVec to_visit{ term };
  TermVec cached_children;
  Term t;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();
    if (cache.find(t) == cache.end())
    {
      // doesn't get updated yet, just marking as visited
      cache[t] = t;
      to_visit.push_back(t);
      for (auto c : t)
      {
        to_visit.push_back(c);
      }
    }
    else
    {
      cached_children.clear();
      for (auto c : t)
      {
        cached_children.push_back(cache.at(c));
      }

      // const arrays have children but don't need to be rebuilt
      // (they're constructed in a particular way anyway)
      if (cached_children.size() && !t->is_value())
      {
        cache[t] = make_term(t->get_op(), cached_children);
      }
    }
  }

  return cache.at(term);
}

TermVec AbsSmtSolver::substitute_terms(
    const TermVec & terms, const UnorderedTermMap & substitution_map) const
{
  TermVec res;
  res.reserve(terms.size());
  for (auto t : terms)
  {
    res.push_back(substitute(t, substitution_map));
  }
  return res;
}

void AbsSmtSolver::dump_smt2(std::string /* filename */) const
{
  throw NotImplementedException("Dumping to a file is not supported by "
                                + to_string(solver_enum));
}

SolverEnum AbsSmtSolver::get_solver_enum() const { return solver_enum; }

}  // namespace smt
