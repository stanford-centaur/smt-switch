/*!
 * \file logging_solver.cpp
 * \brief Class that wraps another SmtSolver and tracks the term DAG by wrapping
 *        sorts and terms and performs hash-consing
 * \author Makai Mann
 * \author Clark Barrett
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/logging_solver.h"

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "smt-switch/datatype.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/logging_datatype.h"
#include "smt-switch/logging_sort.h"
#include "smt-switch/logging_term.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/sort_inference.h"
#include "smt-switch/term.h"
#include "smt-switch/term_hashtable.h"
#include "smt-switch/utils.h"

namespace smt {

namespace {

/** Casts a handle as backend_pointer_cast does, but refuses a null one
 *  @param h the handle a caller passed to the solver
 *  @param msg the message to throw if h is null
 *  @return h as a T
 *  @throws IncorrectUsageException if h is null or was made by another
 *          solver
 */
template <class T, class Base>
std::shared_ptr<T> non_null_cast(const std::shared_ptr<Base> & h,
                                 const std::string & msg)
{
  if (!h)
  {
    throw IncorrectUsageException(msg);
  }
  return backend_pointer_cast<T>(h);
}

}  // namespace

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
    sub_sorts.push_back(
        non_null_cast<LoggingSort>(s, "Cannot make a sort from a null sort")
            ->wrapped_sort);
  }
  Sort sort = wrapped_solver->make_sort(sk, sub_sorts);
  return make_logging_sort(sk, sort, sorts);
}

Sort LoggingSolver::make_sort(const Sort & sort_con,
                              const SortVec & sorts) const
{
  Sort sub_sort_con = non_null_cast<LoggingSort>(
                          sort_con, "Cannot apply a null sort constructor")
                          ->wrapped_sort;

  // convert to sorts stored by LoggingSorts
  SortVec sub_sorts;
  for (auto s : sorts)
  {
    sub_sorts.push_back(non_null_cast<LoggingSort>(
                            s, "Cannot apply a sort constructor to a null sort")
                            ->wrapped_sort);
  }

  Sort ressort = wrapped_solver->make_sort(sub_sort_con, sub_sorts);
  return make_uninterpreted_logging_sort(ressort, sort_con, sorts);
}

Sort LoggingSolver::make_sort(const DatatypeDecl & d) const
{
  std::shared_ptr<LoggingDatatypeDecl> ld = non_null_cast<LoggingDatatypeDecl>(
      d, "Cannot make a sort from a null datatype declaration");
  Sort wrapped_sort = wrapped_solver->make_sort(ld->wrapped_decl);
  return std::make_shared<DatatypeLoggingSort>(wrapped_sort,
                                               copy_for_sort(*ld));
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
  std::shared_ptr<LoggingDatatypeDecl> ldt = non_null_cast<LoggingDatatypeDecl>(
      dt, "Cannot add a constructor to a null datatype declaration");
  std::shared_ptr<LoggingDatatypeConstructorDecl> lcon =
      non_null_cast<LoggingDatatypeConstructorDecl>(
          con, "Cannot add a null constructor declaration");
  wrapped_solver->add_constructor(ldt->wrapped_decl, lcon->wrapped_decl);
  ldt->constructors.push_back(lcon);
}

void LoggingSolver::add_selector(DatatypeConstructorDecl & dt,
                                 const std::string & name,
                                 const Sort & s) const
{
  std::shared_ptr<LoggingDatatypeConstructorDecl> lcon =
      non_null_cast<LoggingDatatypeConstructorDecl>(
          dt, "Cannot add a selector to a null constructor declaration");
  wrapped_solver->add_selector(
      lcon->wrapped_decl,
      name,
      non_null_cast<LoggingSort>(s, "Cannot add a selector of a null sort")
          ->wrapped_sort);
  lcon->selectors.push_back({ name, s });
}

void LoggingSolver::add_selector_self(DatatypeConstructorDecl & dt,
                                      const std::string & name) const
{
  std::shared_ptr<LoggingDatatypeConstructorDecl> lcon =
      non_null_cast<LoggingDatatypeConstructorDecl>(
          dt, "Cannot add a selector to a null constructor declaration");
  wrapped_solver->add_selector_self(lcon->wrapped_decl, name);
  // the datatype's own sort does not exist yet, so it is left null
  lcon->selectors.push_back({ name, nullptr });
}

Term LoggingSolver::get_constructor(const Sort & s, std::string name) const
{
  Term wrapped = wrapped_solver->get_constructor(
      non_null_cast<LoggingSort>(s, "Cannot get a constructor of a null sort")
          ->wrapped_sort,
      name);
  SortVec domain;
  for (const LoggingSelectorDecl & sel : find_constructor(s, name)->selectors)
  {
    domain.push_back(sel.sort ? sel.sort : s);
  }
  return make_component(
      wrapped, CONSTRUCTOR, domain, s, smtlib_quote_symbol(name));
}

Term LoggingSolver::get_tester(const Sort & s, std::string name) const
{
  Term wrapped = wrapped_solver->get_tester(
      non_null_cast<LoggingSort>(s, "Cannot get a tester of a null sort")
          ->wrapped_sort,
      name);
  return make_component(wrapped,
                        TESTER,
                        SortVec{ s },
                        make_sort(BOOL),
                        "(_ is " + smtlib_quote_symbol(name) + ")");
}

Term LoggingSolver::get_selector(const Sort & s,
                                 std::string con,
                                 std::string name) const
{
  Term wrapped = wrapped_solver->get_selector(
      non_null_cast<LoggingSort>(s, "Cannot get a selector of a null sort")
          ->wrapped_sort,
      con,
      name);
  for (const LoggingSelectorDecl & sel : find_constructor(s, con)->selectors)
  {
    if (sel.name == name)
    {
      return make_component(wrapped,
                            SELECTOR,
                            SortVec{ s },
                            sel.sort ? sel.sort : s,
                            smtlib_quote_symbol(name));
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
        non_null_cast<LoggingDatatypeDecl>(
            d, "Cannot make a sort from a null datatype declaration")
            ->wrapped_decl);
  }
  SortVec wrapped_sorts = wrapped_solver->make_datatype_sorts(wrapped_decls);
  SortVec res;
  res.reserve(decls.size());
  for (std::size_t i = 0; i < decls.size(); ++i)
  {
    res.push_back(std::make_shared<DatatypeLoggingSort>(
        wrapped_sorts[i],
        copy_for_sort(
            *std::static_pointer_cast<LoggingDatatypeDecl>(decls[i]))));
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

std::shared_ptr<LoggingDatatypeDecl> LoggingSolver::copy_for_sort(
    const LoggingDatatypeDecl & d) const
{
  auto copy = std::make_shared<LoggingDatatypeDecl>(d.wrapped_decl, d.name);
  for (const auto & con : d.constructors)
  {
    auto con_copy = std::make_shared<LoggingDatatypeConstructorDecl>(
        con->wrapped_decl, con->name);
    con_copy->selectors = con->selectors;
    copy->constructors.push_back(con_copy);
  }
  return copy;
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
  std::shared_ptr<LoggingSort> lsort =
      non_null_cast<LoggingSort>(sort, "Cannot make a value of a null sort");
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
  std::shared_ptr<LoggingSort> lsort =
      non_null_cast<LoggingSort>(sort, "Cannot make a value of a null sort");
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
  std::shared_ptr<LoggingSort> lsort =
      non_null_cast<LoggingSort>(sort, "Cannot make a value of a null sort");
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
  std::shared_ptr<LoggingSort> lsort =
      non_null_cast<LoggingSort>(sort, "Cannot make a value of a null sort");
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
  std::shared_ptr<LoggingTerm> lval = non_null_cast<LoggingTerm>(
      val, "Cannot make a constant array from a null term");
  std::shared_ptr<LoggingSort> lsort = non_null_cast<LoggingSort>(
      sort, "Cannot make a constant array of a null sort");
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
  std::shared_ptr<LoggingSort> lsort =
      non_null_cast<LoggingSort>(sort, "Cannot make a symbol of a null sort");
  Term wrapped_sym = wrapped_solver->make_symbol(name, lsort->wrapped_sort);
  Term res = std::make_shared<LoggingTerm>(wrapped_sym,
                                           sort,
                                           Op(),
                                           TermVec{},
                                           smtlib_quote_symbol(name),
                                           /* symbol */ true,
                                           next_term_id);

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
  std::shared_ptr<LoggingSort> lsort = non_null_cast<LoggingSort>(
      sort, "Cannot make a parameter of a null sort");
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
    std::shared_ptr<LoggingTerm> ltt = non_null_cast<LoggingTerm>(
        tt, "Cannot apply " + op.to_string() + " to a null term");
    // A LoggingTerm of another LoggingSolver casts, but is not in this one's
    // hash table, nor is one made before a reset.
    if (!hashtable->contains(tt))
    {
      detail::throw_foreign_handle(tt);
    }
    lterms.push_back(ltt->wrapped_term);
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
  std::shared_ptr<LoggingTerm> lt =
      non_null_cast<LoggingTerm>(t, "Cannot get the value of a null term");
  Sort sort = t->get_sort();
  if (sort->get_sort_kind() == ARRAY)
  {
    Term out_const_base;
    UnorderedTermMap pairs = get_array_values(t, out_const_base);
    if (!out_const_base)
    {
      throw SolverException(
          "Wrapped solver did not provide constant base. Please use "
          "get_array_values instead of get_value of an array");
    }
    Term res = make_term(out_const_base, sort);
    for (auto elem : pairs)
    {
      res = make_term(Store, res, elem.first, elem.second);
    }
    return res;
  }

  return wrap_value(wrapped_solver->get_value(lt->wrapped_term), sort);
}

Term LoggingSolver::wrap_value(const Term & wrapped_val,
                               const Sort & sort) const
{
  Op op = wrapped_val->get_op();
  if (op.prim_op == Apply_Constructor)
  {
    // the constructor comes first, then its arguments in selector order
    TermVec wrapped_children(wrapped_val->begin(), wrapped_val->end());
    std::string cons = wrapped_children[0]->get_constructor_name();
    Datatype dt = sort->get_datatype();
    std::vector<std::string> selectors = dt->get_selector_names(cons);
    TermVec children{ get_constructor(sort, cons) };
    for (std::size_t i = 1; i < wrapped_children.size(); ++i)
    {
      children.push_back(wrap_value(
          wrapped_children[i], dt->get_selector_sort(cons, selectors[i - 1])));
    }
    return make_term(op, children);
  }
  // The value was not created through the smt-switch API, so the
  // LoggingSolver cannot recover an Op or children for it
  if (!op.is_null())
  {
    throw NotImplementedException(
        "LoggingSolver does not support get_value for a "
        + to_string(sort->get_sort_kind()) + " value that is not a leaf");
  }
  Term res = std::make_shared<LoggingTerm>(
      wrapped_val, sort, Op(), TermVec{}, next_term_id);

  // check hash table
  // lookup modifies res in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
    next_term_id++;
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
      throw SolverException(
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
  std::shared_ptr<LoggingTerm> larr =
      non_null_cast<LoggingTerm>(arr, "Cannot get the values of a null array");
  Sort arrsort = arr->get_sort();
  Sort idxsort = arrsort->get_indexsort();
  Sort elemsort = arrsort->get_elemsort();
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
    // An entry is wrapped with no op, which claims it is a leaf, so only a
    // value can be wrapped.
    if (!elem.first->is_value() || !elem.second->is_value())
    {
      throw NotImplementedException(
          "LoggingSolver can't wrap array model entry "
          + elem.first->to_string() + " -> " + elem.second->to_string()
          + ", which is not a value");
    }

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

void LoggingSolver::do_assert(const Term & t)
{
  std::shared_ptr<LoggingTerm> lt =
      non_null_cast<LoggingTerm>(t, "Cannot assert a null term");
  wrapped_solver->assert_formula(lt->wrapped_term);
}

Result LoggingSolver::check_sat() { return wrapped_solver->check_sat(); }

Result LoggingSolver::do_check_sat_assuming(const TermVec & assumptions)
{
  // only needs to remember the latest set of assumptions
  assumption_cache->clear();
  TermVec lassumps;
  std::shared_ptr<LoggingTerm> la;
  for (auto a : assumptions)
  {
    la = non_null_cast<LoggingTerm>(a, "Cannot assume a null term");
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
