/*********************                                                        */
/*! \file logging_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that wraps another SmtSolver and tracks the term DAG by
**        wrapping sorts and terms and performs hash-consing.
**
**/

#include "logging_solver.h"

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "exceptions.h"
#include "logging_datatype.h"
#include "logging_sort.h"
#include "logging_term.h"
#include "smt_defs.h"
#include "sort.h"
#include "sort_inference.h"
#include "term.h"
#include "term_hashtable.h"
#include "utils.h"

namespace smt {

/* These are the only sortkinds that are supported for get_value
   Terms returned by get_value were not created through the
   smt-switch API, so the LoggingSolver needs to recover some
   information. Most SortKinds are not an issue because they
   have no Op or children
 */
const std::unordered_set<SortKind> supported_sortkinds_for_get_value(
    { BOOL, BV, INT, STRING, REAL, ARRAY });

/* LoggingSolver */

// implementations

LoggingSolver::LoggingSolver(SmtSolver s)
    : AbsSmtSolver(s->get_solver_enum()),
      wrapped_solver(std::move(s)),
      hashtable(new TermHashTable()),
      assumption_cache(new UnorderedTermMap())
{
}

Sort LoggingSolver::make_sort(const std::string name, std::uint64_t arity) const
{
  Sort wrapped_sort = wrapped_solver->make_sort(name, arity);
  return make_uninterpreted_logging_sort(wrapped_sort, name, arity);
}

Sort LoggingSolver::make_sort(const SortKind sk) const
{
  Sort sort = wrapped_solver->make_sort(sk);
  return make_logging_sort(sk, sort);
}

Sort LoggingSolver::make_sort(const SortKind sk, std::uint64_t size) const
{
  Sort sort = wrapped_solver->make_sort(sk, size);
  return make_logging_sort(sk, sort, size);
}

Sort LoggingSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  // convert to sorts stored by LoggingSorts
  SortVec sub_sorts;
  for (auto s : sorts)
  {
    sub_sorts.push_back(backend_pointer_cast<LoggingSort>(s)->wrapped_sort);
  }
  Sort sort = wrapped_solver->make_sort(sk, sub_sorts);
  return make_logging_sort(sk, sort, sorts);
}

Sort LoggingSolver::make_sort(const Sort & sort_con,
                              const SortVec & sorts) const
{
  Sort sub_sort_con = backend_pointer_cast<LoggingSort>(sort_con)->wrapped_sort;

  // convert to sorts stored by LoggingSorts
  SortVec sub_sorts;
  for (auto s : sorts)
  {
    sub_sorts.push_back(backend_pointer_cast<LoggingSort>(s)->wrapped_sort);
  }

  Sort ressort = wrapped_solver->make_sort(sub_sort_con, sub_sorts);
  return make_uninterpreted_logging_sort(
      ressort, sort_con->get_uninterpreted_name(), sorts);
}

Sort LoggingSolver::make_sort(const DatatypeDecl & d) const
{
  std::shared_ptr<LoggingDatatypeDecl> ld =
      backend_pointer_cast<LoggingDatatypeDecl>(d);
  Sort wrapped_sort = wrapped_solver->make_sort(ld->wrapped_decl);
  return std::make_shared<DatatypeLoggingSort>(wrapped_sort, ld);
}

DatatypeDecl LoggingSolver::make_datatype_decl(const std::string & s) const
{
  return std::make_shared<LoggingDatatypeDecl>(
      wrapped_solver->make_datatype_decl(s), s);
}

DatatypeConstructorDecl LoggingSolver::make_datatype_constructor_decl(
    const std::string s) const
{
  return std::make_shared<LoggingDatatypeConstructorDecl>(
      wrapped_solver->make_datatype_constructor_decl(s), s);
}

void LoggingSolver::add_constructor(DatatypeDecl & dt,
                                    const DatatypeConstructorDecl & con) const
{
  std::shared_ptr<LoggingDatatypeDecl> ldt =
      backend_pointer_cast<LoggingDatatypeDecl>(dt);
  std::shared_ptr<LoggingDatatypeConstructorDecl> lcon =
      backend_pointer_cast<LoggingDatatypeConstructorDecl>(con);
  wrapped_solver->add_constructor(ldt->wrapped_decl, lcon->wrapped_decl);
  ldt->constructors.push_back(lcon);
}

void LoggingSolver::add_selector(DatatypeConstructorDecl & dt,
                                 const std::string & name,
                                 const Sort & s) const
{
  std::shared_ptr<LoggingDatatypeConstructorDecl> lcon =
      backend_pointer_cast<LoggingDatatypeConstructorDecl>(dt);
  wrapped_solver->add_selector(
      lcon->wrapped_decl,
      name,
      backend_pointer_cast<LoggingSort>(s)->wrapped_sort);
  lcon->selectors.push_back({ name, s });
}

void LoggingSolver::add_selector_self(DatatypeConstructorDecl & dt,
                                      const std::string & name) const
{
  std::shared_ptr<LoggingDatatypeConstructorDecl> lcon =
      backend_pointer_cast<LoggingDatatypeConstructorDecl>(dt);
  wrapped_solver->add_selector_self(lcon->wrapped_decl, name);
  // the datatype's own sort does not exist yet, so it is left null
  lcon->selectors.push_back({ name, nullptr });
}

Term LoggingSolver::get_constructor(const Sort & s, std::string name) const
{
  Term wrapped = wrapped_solver->get_constructor(
      backend_pointer_cast<LoggingSort>(s)->wrapped_sort, name);
  SortVec domain;
  for (const LoggingSelectorDecl & sel : find_constructor(s, name)->selectors)
  {
    domain.push_back(sel.sort ? sel.sort : s);
  }
  return make_component(wrapped, CONSTRUCTOR, domain, s, name);
}

Term LoggingSolver::get_tester(const Sort & s, std::string name) const
{
  Term wrapped = wrapped_solver->get_tester(
      backend_pointer_cast<LoggingSort>(s)->wrapped_sort, name);
  return make_component(
      wrapped, TESTER, SortVec{ s }, make_sort(BOOL), "(_ is " + name + ")");
}

Term LoggingSolver::get_selector(const Sort & s,
                                 std::string con,
                                 std::string name) const
{
  Term wrapped = wrapped_solver->get_selector(
      backend_pointer_cast<LoggingSort>(s)->wrapped_sort, con, name);
  for (const LoggingSelectorDecl & sel : find_constructor(s, con)->selectors)
  {
    if (sel.name == name)
    {
      return make_component(
          wrapped, SELECTOR, SortVec{ s }, sel.sort ? sel.sort : s, name);
    }
  }
  throw IncorrectUsageException("Constructor " + con + " has no selector "
                                + name);
}

SortVec LoggingSolver::make_datatype_sorts(
    const std::vector<DatatypeDecl> & decls) const
{
  std::vector<DatatypeDecl> wrapped_decls;
  wrapped_decls.reserve(decls.size());
  for (const DatatypeDecl & d : decls)
  {
    wrapped_decls.push_back(
        backend_pointer_cast<LoggingDatatypeDecl>(d)->wrapped_decl);
  }
  SortVec wrapped_sorts = wrapped_solver->make_datatype_sorts(wrapped_decls);
  SortVec res;
  res.reserve(decls.size());
  for (std::size_t i = 0; i < decls.size(); ++i)
  {
    res.push_back(std::make_shared<DatatypeLoggingSort>(
        wrapped_sorts[i],
        std::static_pointer_cast<LoggingDatatypeDecl>(decls[i])));
  }
  return res;
}

std::shared_ptr<LoggingDatatypeConstructorDecl> LoggingSolver::find_constructor(
    const Sort & s, const std::string & name) const
{
  for (const std::shared_ptr<LoggingDatatypeConstructorDecl> & con :
       std::static_pointer_cast<DatatypeLoggingSort>(s)->decl->constructors)
  {
    if (con->name == name)
    {
      return con;
    }
  }
  throw IncorrectUsageException("Constructor " + name + " not found");
}

Term LoggingSolver::make_component(const Term & wrapped,
                                   SortKind sk,
                                   const SortVec & domain,
                                   const Sort & codomain,
                                   const std::string & repr) const
{
  Sort sort = std::make_shared<DatatypeComponentLoggingSort>(
      sk, wrapped->get_sort(), domain, codomain);
  Term res = std::make_shared<LoggingTerm>(wrapped, sort, repr, next_term_id);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroys the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
    next_term_id++;
  }

  return res;
}

Term LoggingSolver::make_term(bool b) const
{
  Term wrapped_res = wrapped_solver->make_term(b);
  Sort boolsort = make_logging_sort(BOOL, wrapped_res->get_sort());
  Term res = std::make_shared<LoggingTerm>(
      wrapped_res, boolsort, Op(), TermVec{}, next_term_id);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroys the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
    next_term_id++;
  }

  return res;
}

Term LoggingSolver::make_term(std::int64_t i, const Sort & sort) const
{
  std::shared_ptr<LoggingSort> lsort = backend_pointer_cast<LoggingSort>(sort);
  Term wrapped_res = wrapped_solver->make_term(i, lsort->wrapped_sort);
  Term res = std::make_shared<LoggingTerm>(
      wrapped_res, sort, Op(), TermVec{}, next_term_id);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
    next_term_id++;
  }

  return res;
}

Term LoggingSolver::make_term(const std::string & s,
                              bool useEscSequences,
                              const Sort & sort) const
{
  std::shared_ptr<LoggingSort> lsort = backend_pointer_cast<LoggingSort>(sort);
  Term wrapped_res =
      wrapped_solver->make_term(s, useEscSequences, lsort->wrapped_sort);
  Term res = std::make_shared<LoggingTerm>(
      wrapped_res, sort, Op(), TermVec{}, next_term_id);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
    next_term_id++;
  }

  return res;
}

Term LoggingSolver::make_term(const std::wstring & s, const Sort & sort) const
{
  std::shared_ptr<LoggingSort> lsort = backend_pointer_cast<LoggingSort>(sort);
  Term wrapped_res = wrapped_solver->make_term(s, lsort->wrapped_sort);
  Term res = std::make_shared<LoggingTerm>(
      wrapped_res, sort, Op(), TermVec{}, next_term_id);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
    next_term_id++;
  }

  return res;
}

Term LoggingSolver::make_term(const std::string name,
                              const Sort & sort,
                              std::uint64_t base) const
{
  std::shared_ptr<LoggingSort> lsort = backend_pointer_cast<LoggingSort>(sort);
  Term wrapped_res = wrapped_solver->make_term(name, lsort->wrapped_sort, base);
  Term res = std::make_shared<LoggingTerm>(
      wrapped_res, sort, Op(), TermVec{}, next_term_id);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
    next_term_id++;
  }

  return res;
}

Term LoggingSolver::make_term(const Term & val, const Sort & sort) const
{
  std::shared_ptr<LoggingTerm> lval = backend_pointer_cast<LoggingTerm>(val);
  std::shared_ptr<LoggingSort> lsort = backend_pointer_cast<LoggingSort>(sort);
  Term wrapped_res =
      wrapped_solver->make_term(lval->wrapped_term, lsort->wrapped_sort);
  // this make_term is for constant arrays
  if (sort->get_sort_kind() != ARRAY)
  {
    throw IncorrectUsageException(
        "make_term(Term, Sort) is for creating constant arrays.\nExpecting "
        "array sort but got: "
        + sort->to_string());
  }
  // the constant value must be the child
  Term res = std::make_shared<LoggingTerm>(
      wrapped_res, sort, Op(), TermVec{ val }, next_term_id);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
    next_term_id++;
  }

  return res;
}

Term LoggingSolver::make_symbol(const std::string name, const Sort & sort)
{
  std::shared_ptr<LoggingSort> lsort = backend_pointer_cast<LoggingSort>(sort);
  Term wrapped_sym = wrapped_solver->make_symbol(name, lsort->wrapped_sort);
  // bool true means it's a symbol
  Term res = std::make_shared<LoggingTerm>(
      wrapped_sym, sort, Op(), TermVec{}, name, true, next_term_id);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
    next_term_id++;
  }

  symbol_table[name] = res;

  return res;
}

Term LoggingSolver::get_symbol(const std::string & name) const
{
  auto it = symbol_table.find(name);
  if (it == symbol_table.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist.");
  }
  return it->second;
}

Term LoggingSolver::make_param(const std::string name, const Sort & sort) const
{
  std::shared_ptr<LoggingSort> lsort = backend_pointer_cast<LoggingSort>(sort);
  Term wrapped_param = wrapped_solver->make_param(name, lsort->wrapped_sort);
  // bool false means it's not a symbol
  Term res = std::make_shared<LoggingTerm>(
      wrapped_param, sort, Op(), TermVec{}, name, false, next_term_id);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
    next_term_id++;
  }

  return res;
}

Term LoggingSolver::make_term(const Op op, const TermVec & terms) const
{
  TermVec lterms;
  for (auto tt : terms)
  {
    std::shared_ptr<LoggingTerm> ltt = backend_pointer_cast<LoggingTerm>(tt);
    lterms.push_back(ltt->wrapped_term);

    // check that children are already in the hash table
    assert(hashtable->contains(tt));
  }
  Term wrapped_res = wrapped_solver->make_term(op, lterms);
  // Note: for convenience there's a version of compute_sort that takes terms
  // since these are already in a vector, just let it unpack the sorts
  Sort res_logging_sort = compute_sort(op, this, terms);
  Term res = std::make_shared<LoggingTerm>(
      wrapped_res, res_logging_sort, op, terms, next_term_id);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
    next_term_id++;
  }

  return res;
}

Term LoggingSolver::get_value(const Term & t) const
{
  Term res;
  SortKind sk = t->get_sort()->get_sort_kind();
  if (supported_sortkinds_for_get_value.find(sk)
      == supported_sortkinds_for_get_value.end())
  {
    throw NotImplementedException(
        "LoggingSolver does not support get_value for " + to_string(sk));
  }

  std::shared_ptr<LoggingTerm> lt = backend_pointer_cast<LoggingTerm>(t);
  if (t->get_sort()->get_sort_kind() != ARRAY)
  {
    Term wrapped_val = wrapped_solver->get_value(lt->wrapped_term);
    res = std::make_shared<LoggingTerm>(
        wrapped_val, t->get_sort(), Op(), TermVec{}, next_term_id);

    // check hash table
    // lookup modifies term in place and returns true if it's a known term
    // i.e. returns existing term and destroying the unnecessary new one
    if (!hashtable->lookup(res))
    {
      // this is the first time this term was created
      hashtable->insert(res);
      next_term_id++;
    }
  }
  else
  {
    Term out_const_base;
    UnorderedTermMap pairs = get_array_values(t, out_const_base);
    if (!out_const_base)
    {
      throw InternalSolverException(
          "Wrapped solver did not provide constant base. Please use "
          "get_array_values instead of get_value of an array");
    }
    res = make_term(out_const_base, t->get_sort());
    for (auto elem : pairs)
    {
      res = make_term(Store, res, elem.first, elem.second);
    }
  }

  return res;
}

void LoggingSolver::get_unsat_assumptions(UnorderedTermSet & out) const
{
  UnorderedTermSet underlying_core;
  wrapped_solver->get_unsat_assumptions(underlying_core);
  for (auto c : underlying_core)
  {
    // these are the terms that were used in check_sat_assuming, and
    // assumption_cache stored a mapping so we can recover the logging term
    if (assumption_cache->find(c) == assumption_cache->end())
    {
      throw InternalSolverException(
          "Got an element in the unsat core that was not cached from "
          "check_sat_assuming in LoggingSolver.");
    }
    Term log_c = assumption_cache->at(c);
    out.insert(log_c);
  }
}

UnorderedTermMap LoggingSolver::get_array_values(const Term & arr,
                                                 Term & out_const_base) const
{
  Sort arrsort = arr->get_sort();
  Sort idxsort = arrsort->get_indexsort();
  Sort elemsort = arrsort->get_elemsort();
  std::shared_ptr<LoggingTerm> larr = backend_pointer_cast<LoggingTerm>(arr);
  UnorderedTermMap assignments;
  Term wrapped_out_const_base;
  UnorderedTermMap wrapped_assignments = wrapped_solver->get_array_values(
      larr->wrapped_term, wrapped_out_const_base);
  if (wrapped_out_const_base)
  {
    if (wrapped_out_const_base->get_sort()->get_sort_kind() == ARRAY)
    {
      throw NotImplementedException(
          "const base for multidimensional array not implemented in "
          "LoggingSolver");
    }
    out_const_base = std::make_shared<LoggingTerm>(
        wrapped_out_const_base, elemsort, Op(), TermVec{}, next_term_id);
    // check hash table
    // lookup modifies term in place and returns true if it's a known term
    // i.e. returns existing term and destroys the unnecessary new one
    if (!hashtable->lookup(out_const_base))
    {
      // this is the first time this term was created
      hashtable->insert(out_const_base);
      next_term_id++;
    }
  }

  Term idx;
  Term val;
  for (auto elem : wrapped_assignments)
  {
    // expecting values in assignment map
    assert(elem.first->is_value());
    assert(elem.second->is_value());

    idx = std::make_shared<LoggingTerm>(
        elem.first, idxsort, Op(), TermVec{}, next_term_id);
    if (!hashtable->lookup(idx))
    {
      // this is the first time this term was created
      hashtable->insert(idx);
      next_term_id++;
    }

    val = std::make_shared<LoggingTerm>(
        elem.second, elemsort, Op(), TermVec{}, next_term_id);
    if (!hashtable->lookup(val))
    {
      // this is the first time this term was created
      hashtable->insert(val);
      next_term_id++;
    }

    assignments[idx] = val;
  }

  return assignments;
}

void LoggingSolver::do_reset()
{
  // these hold wrapped terms, which may not outlive the wrapped solver's
  // reset
  hashtable->clear();
  symbol_table.clear();
  assumption_cache->clear();
  wrapped_solver->reset();
}

// dispatched to underlying solver

void LoggingSolver::set_opt(const std::string option, const std::string value)
{
  wrapped_solver->set_opt(option, value);
}

void LoggingSolver::set_logic(const std::string logic)
{
  wrapped_solver->set_logic(logic);
}

void LoggingSolver::assert_formula(const Term & t)
{
  std::shared_ptr<LoggingTerm> lt = backend_pointer_cast<LoggingTerm>(t);
  wrapped_solver->assert_formula(lt->wrapped_term);
}

Result LoggingSolver::check_sat() { return wrapped_solver->check_sat(); }

Result LoggingSolver::check_sat_assuming(const TermVec & assumptions)
{
  // only needs to remember the latest set of assumptions
  assumption_cache->clear();
  TermVec lassumps;
  std::shared_ptr<LoggingTerm> la;
  for (auto a : assumptions)
  {
    la = backend_pointer_cast<LoggingTerm>(a);
    lassumps.push_back(la->wrapped_term);
    // store a mapping from the wrapped term to the logging term
    (*assumption_cache)[la->wrapped_term] = la;
  }
  return wrapped_solver->check_sat_assuming(lassumps);
}

void LoggingSolver::do_push(std::uint64_t num) { wrapped_solver->push(num); }

void LoggingSolver::do_pop(std::uint64_t num) { wrapped_solver->pop(num); }

std::uint64_t LoggingSolver::get_context_level() const
{
  return wrapped_solver->get_context_level();
}

void LoggingSolver::dump_smt2(std::string filename) const
{
  wrapped_solver->dump_smt2(filename);
}

void LoggingSolver::do_reset_assertions()
{
  wrapped_solver->reset_assertions();
}

}  // namespace smt
