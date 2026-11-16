/*!
 * \file solver.cpp
 * \brief Abstract interface for SMT solvers
 * \author Makai Mann
 * \author Clark Barrett
 * \author Áron Ricardo Perez-Lopez
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/solver.h"

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <list>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

// TODO: Implement a generic visitor

AbsSmtSolver::AbsSmtSolver(SolverEnum se) : solver_enum(se) {}

void AbsSmtSolver::assert_formula(const Term & t)
{
  // compares sorts rather than kinds, as some solvers alias Bool to another
  // sort
  if (!t)
  {
    throw IncorrectUsageException("Cannot assert a null term");
  }
  if (t->get_sort() != make_sort(BOOL))
  {
    throw IncorrectUsageException("Expecting a Boolean assertion but got: "
                                  + t->to_string());
  }
  do_assert(t);
}

Result AbsSmtSolver::check_sat_assuming(const TermVec & assumptions)
{
  // Every assumption is checked before any is assumed: one assumed before a
  // refused one would still hold for the next check. The check compares
  // sorts rather than kinds, as some solvers alias Bool to another sort.
  const Sort boolsort = make_sort(BOOL);
  for (const Term & a : assumptions)
  {
    if (!a)
    {
      throw IncorrectUsageException("Cannot assume a null term");
    }
    if (a->get_sort() != boolsort)
    {
      throw IncorrectUsageException("Expecting Boolean assumptions but got: "
                                    + a->to_string());
    }
  }
  return do_check_sat_assuming(assumptions);
}

Result AbsSmtSolver::check_sat_assuming_list(
    const std::list<Term> & assumptions)
{
  return check_sat_assuming(assumptions);
}

Result AbsSmtSolver::check_sat_assuming_set(
    const UnorderedTermSet & assumptions)
{
  return check_sat_assuming(assumptions);
}

void AbsSmtSolver::push(std::uint64_t num)
{
  do_push(num);
  context_level += num;
}

void AbsSmtSolver::pop(std::uint64_t num)
{
  if (num > get_context_level())
  {
    throw IncorrectUsageException("Can't pop " + std::to_string(num)
                                  + " contexts at context level "
                                  + std::to_string(get_context_level()));
  }
  do_pop(num);
  context_level -= num;
}

std::uint64_t AbsSmtSolver::get_context_level() const { return context_level; }

void AbsSmtSolver::pop_all() { pop(get_context_level()); }

void AbsSmtSolver::reset()
{
  do_reset();
  context_level = 0;
}

void AbsSmtSolver::reset_assertions()
{
  do_reset_assertions();
  context_level = 0;
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

DatatypeDecl AbsSmtSolver::make_datatype_decl(const std::string & /* s */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

DatatypeConstructorDecl AbsSmtSolver::make_datatype_constructor_decl(
    const std::string /* s */) const
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
    const std::vector<DatatypeDecl> & /* decls */) const
{
  throw NotImplementedException("make_datatype_sorts is not implemented by "
                                + to_string(solver_enum));
}

Sort AbsSmtSolver::make_datatype_sort(const DatatypeDecl & decl) const
{
  SortVec datatype_sorts = make_datatype_sorts({ decl });
  if (datatype_sorts.size() != 1)
  {
    throw SolverException("make_datatype_sorts gave "
                          + std::to_string(datatype_sorts.size())
                          + " sorts for one datatype declaration");
  }
  return datatype_sorts[0];
}

Term AbsSmtSolver::substitute(const Term term,
                              const UnorderedTermMap & substitution_map) const
{
  // each term's result once it is known; a term is rebuilt the second time
  // it comes off the stack, after its children
  UnorderedTermMap cache;
  UnorderedTermSet visited;
  TermVec to_visit{ term };
  TermVec cached_children;
  Term t;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();
    if (cache.find(t) != cache.end())
    {
      continue;
    }
    // a key is replaced whole, whatever it is made of
    auto it = substitution_map.find(t);
    if (it != substitution_map.end())
    {
      cache[t] = it->second;
      continue;
    }
    if (visited.insert(t).second)
    {
      to_visit.push_back(t);
      for (auto c : t)
      {
        to_visit.push_back(c);
      }
      continue;
    }
    cached_children.clear();
    for (auto c : t)
    {
      cached_children.push_back(cache.at(c));
    }

    // const arrays have children but don't need to be rebuilt
    // (they're constructed in a particular way anyway)
    cache[t] = cached_children.size() && !t->is_value()
                   ? make_term(t->get_op(), cached_children)
                   : t;
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

Term AbsSmtSolver::make_nary_term(const Op & op, const TermVec & terms) const
{
  std::size_t size = terms.size();
  if (size < 2)
  {
    throw IncorrectUsageException("Can't apply " + op.to_string() + " to "
                                  + std::to_string(size) + " terms.");
  }
  if (is_left_assoc(op.prim_op))
  {
    Term res = terms[0];
    for (std::size_t i = 1; i < size; ++i)
    {
      res = make_term(op, res, terms[i]);
    }
    return res;
  }
  else if (is_right_assoc(op.prim_op))
  {
    Term res = terms[size - 1];
    for (std::size_t i = 1; i < size; ++i)
    {
      res = make_term(op, terms[size - 1 - i], res);
    }
    return res;
  }

  TermVec conjuncts;
  if (is_chainable(op.prim_op))
  {
    for (std::size_t i = 0; i + 1 < size; ++i)
    {
      conjuncts.push_back(make_term(op, terms[i], terms[i + 1]));
    }
  }
  else if (is_pairwise(op.prim_op))
  {
    for (std::size_t i = 0; i < size; ++i)
    {
      for (std::size_t j = i + 1; j < size; ++j)
      {
        conjuncts.push_back(make_term(op, terms[i], terms[j]));
      }
    }
  }
  else
  {
    throw IncorrectUsageException("Can't apply " + op.to_string() + " to "
                                  + std::to_string(size) + " terms.");
  }
  return conjuncts.size() == 1 ? conjuncts[0] : make_term(And, conjuncts);
}

void AbsSmtSolver::check_quantifier_binders(const Op & op,
                                            const TermVec & terms)
{
  if (terms.size() < 2)
  {
    throw IncorrectUsageException(op.to_string()
                                  + " takes one or more params and a body");
  }
  for (std::size_t i = 0; i + 1 < terms.size(); ++i)
  {
    if (!terms[i]->is_param())
    {
      throw IncorrectUsageException(op.to_string() + " can only bind a param, "
                                    + "but got " + terms[i]->to_string());
    }
  }
}

bool AbsSmtSolver::parse_bool_opt(const std::string & option,
                                  const std::string & value)
{
  if (value != "true" && value != "false")
  {
    throw IncorrectUsageException("The option " + option
                                  + " takes true or false, not " + value);
  }
  return value == "true";
}

std::chrono::duration<double> AbsSmtSolver::parse_time_limit(
    const std::string & value)
{
  double seconds = 0;
  std::size_t end = 0;
  try
  {
    seconds = std::stod(value, &end);
  }
  catch (const std::logic_error &)
  {
    // std::stod failed, so end is still zero
  }
  if (end == 0 || end != value.size() || !std::isfinite(seconds) || seconds < 0)
  {
    throw IncorrectUsageException(
        "The option time-limit takes a nonnegative number of seconds, not "
        + value);
  }
  // Half of what a clock counting nanoseconds in 64 bits holds, so that a
  // solver adding the limit to the time now cannot overflow; a longer limit
  // is as good as none.
  constexpr double longest =
      std::chrono::duration<double>(std::chrono::nanoseconds::max()).count()
      / 2;
  return std::chrono::duration<double>(std::min(seconds, longest));
}

UnorderedTermMap AbsSmtSolver::store_chain_values(
    const std::vector<std::pair<Term, Term>> & stores)
{
  UnorderedTermMap assignments;
  for (const auto & store : stores)
  {
    // insert keeps the assignment already in the map, so the outermost
    // store, which comes first, is the one that stands
    assignments.insert(store);
  }
  return assignments;
}

}  // namespace smt
