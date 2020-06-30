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
#include "logging_sort.h"
#include "logging_sort_computation.h"
#include "logging_term.h"

#include "utils.h"

using namespace std;

namespace smt {

/* These are the only sortkinds that are supported for get_value
   Terms returned by get_value were not created through the
   smt-switch API, so the LoggingSolver needs to recover some
   information. Most SortKinds are not an issue because they
   have no Op or children
 */
const unordered_set<SortKind> supported_sortkinds_for_get_value(
    { BOOL, BV, INT, REAL, ARRAY });

/* LoggingSolver */

// implementations

LoggingSolver::LoggingSolver(SmtSolver s)
    : AbsSmtSolver(process_solver_enum(s->get_solver_enum())),
      wrapped_solver(s),
      hashtable(new TermHashTable()),
      assumption_cache(new UnorderedTermMap())
{
}

LoggingSolver::~LoggingSolver() {}

Sort LoggingSolver::make_sort(const string name, uint64_t arity) const
{
  Sort wrapped_sort = wrapped_solver->make_sort(name, arity);
  return make_uninterpreted_logging_sort(wrapped_sort, name, arity);
}

Sort LoggingSolver::make_sort(const SortKind sk) const
{
  Sort sort = wrapped_solver->make_sort(sk);
  return make_logging_sort(sk, sort);
}

Sort LoggingSolver::make_sort(const SortKind sk, uint64_t size) const
{
  Sort sort = wrapped_solver->make_sort(sk, size);
  return make_logging_sort(sk, sort, size);
}

Sort LoggingSolver::make_sort(const SortKind sk, const Sort & sort1) const
{
  shared_ptr<LoggingSort> ls1 = static_pointer_cast<LoggingSort>(sort1);
  Sort sort = wrapped_solver->make_sort(sk, ls1->wrapped_sort);
  return make_logging_sort(sk, sort, sort1);
}

Sort LoggingSolver::make_sort(const SortKind sk,
                              const Sort & sort1,
                              const Sort & sort2) const
{
  shared_ptr<LoggingSort> ls1 = static_pointer_cast<LoggingSort>(sort1);
  shared_ptr<LoggingSort> ls2 = static_pointer_cast<LoggingSort>(sort2);
  Sort sort =
      wrapped_solver->make_sort(sk, ls1->wrapped_sort, ls2->wrapped_sort);
  return make_logging_sort(sk, sort, sort1, sort2);
}

Sort LoggingSolver::make_sort(const SortKind sk,
                              const Sort & sort1,
                              const Sort & sort2,
                              const Sort & sort3) const
{
  shared_ptr<LoggingSort> ls1 = static_pointer_cast<LoggingSort>(sort1);

  shared_ptr<LoggingSort> ls2 = static_pointer_cast<LoggingSort>(sort2);
  shared_ptr<LoggingSort> ls3 = static_pointer_cast<LoggingSort>(sort3);
  Sort sort = wrapped_solver->make_sort(
      sk, ls1->wrapped_sort, ls2->wrapped_sort, ls3->wrapped_sort);
  return make_logging_sort(sk, sort, sort1, sort2, sort3);
}

Sort LoggingSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  // convert to sorts stored by LoggingSorts
  SortVec sub_sorts;
  for (auto s : sorts)
  {
    sub_sorts.push_back(static_pointer_cast<LoggingSort>(s)->wrapped_sort);
  }
  Sort sort = wrapped_solver->make_sort(sk, sub_sorts);
  return make_logging_sort(sk, sort, sorts);
}


Sort LoggingSolver::make_sort(const DatatypeDecl & d) const {
  throw NotImplementedException("LoggingSolver::make_sort");
};
DatatypeDecl LoggingSolver::make_datatype_decl(const std::string & s)  {
    throw NotImplementedException("LoggingSolver::make_datatype_decl");
}
DatatypeConstructorDecl LoggingSolver::make_datatype_constructor_decl(
    const std::string s)
{
  throw NotImplementedException(
      "LoggingSolver::make_datatype_constructor_decl");
};
void LoggingSolver::add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const {
  throw NotImplementedException("LoggingSolver::add_constructor");
};
void LoggingSolver::add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const {
  throw NotImplementedException("LoggingSolver::add_selector");
};
void LoggingSolver::add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const {
  throw NotImplementedException("LoggingSolver::add_selector_self");
};

Term LoggingSolver::get_constructor(const Sort & s, std::string name) const  {
  throw NotImplementedException("LoggingSolver::get_constructor");
};
Term LoggingSolver::get_tester(const Sort & s, std::string name) const  {
  throw NotImplementedException("LoggingSolver::get_testeer");
};

Term LoggingSolver::get_selector(const Sort & s, std::string con, std::string name) const  {
  throw NotImplementedException("LoggingSolver::get_selector");
};


Term LoggingSolver::make_term(bool b) const
{
  Term wrapped_res = wrapped_solver->make_term(b);
  Sort boolsort = make_logging_sort(BOOL, wrapped_res->get_sort());
  Term res =
      std::make_shared<LoggingTerm>(wrapped_res, boolsort, Op(), TermVec{});

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
  }

  return res;
}

Term LoggingSolver::make_term(int64_t i, const Sort & sort) const
{
  shared_ptr<LoggingSort> lsort = static_pointer_cast<LoggingSort>(sort);
  Term wrapped_res = wrapped_solver->make_term(i, lsort->wrapped_sort);
  Term res = std::make_shared<LoggingTerm>(wrapped_res, sort, Op(), TermVec{});

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
  }

  return res;
}

Term LoggingSolver::make_term(const string name,
                              const Sort & sort,
                              uint64_t base) const
{
  shared_ptr<LoggingSort> lsort = static_pointer_cast<LoggingSort>(sort);
  Term wrapped_res = wrapped_solver->make_term(name, lsort->wrapped_sort, base);
  Term res = std::make_shared<LoggingTerm>(wrapped_res, sort, Op(), TermVec{});

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
  }

  return res;
}

Term LoggingSolver::make_term(const Term & val, const Sort & sort) const
{
  shared_ptr<LoggingTerm> lval = static_pointer_cast<LoggingTerm>(val);
  shared_ptr<LoggingSort> lsort = static_pointer_cast<LoggingSort>(sort);
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
  Term res =
      std::make_shared<LoggingTerm>(wrapped_res, sort, Op(), TermVec{ val });

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
  }

  return res;
}

Term LoggingSolver::make_symbol(const string name, const Sort & sort)
{
  shared_ptr<LoggingSort> lsort = static_pointer_cast<LoggingSort>(sort);
  Term wrapped_sym = wrapped_solver->make_symbol(name, lsort->wrapped_sort);
  // bool true means it's a symbol
  Term res = std::make_shared<LoggingTerm>(
      wrapped_sym, sort, Op(), TermVec{}, name, true);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
  }

  return res;
}

Term LoggingSolver::make_param(const string name, const Sort & sort)
{
  shared_ptr<LoggingSort> lsort = static_pointer_cast<LoggingSort>(sort);
  Term wrapped_param = wrapped_solver->make_param(name, lsort->wrapped_sort);
  // bool false means it's not a symbol
  Term res = std::make_shared<LoggingTerm>(
      wrapped_param, sort, Op(), TermVec{}, name, false);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
  }

  return res;
}

Term LoggingSolver::make_term(const Op op, const Term & t) const
{
  shared_ptr<LoggingTerm> lt = static_pointer_cast<LoggingTerm>(t);
  Term wrapped_res = wrapped_solver->make_term(op, lt->wrapped_term);
  Sort res_logging_sort =
      compute_sort(op, SortVec{ t->get_sort() }, wrapped_res->get_sort());
  Term res = std::make_shared<LoggingTerm>(
      wrapped_res, res_logging_sort, op, TermVec{ t });

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
  }

  return res;
}

Term LoggingSolver::make_term(const Op op,
                              const Term & t1,
                              const Term & t2) const
{
  shared_ptr<LoggingTerm> lt1 = static_pointer_cast<LoggingTerm>(t1);
  shared_ptr<LoggingTerm> lt2 = static_pointer_cast<LoggingTerm>(t2);
  Term wrapped_res =
      wrapped_solver->make_term(op, lt1->wrapped_term, lt2->wrapped_term);
  Sort res_logging_sort = compute_sort(
      op, SortVec{ t1->get_sort(), t2->get_sort() }, wrapped_res->get_sort());
  Term res(
      new LoggingTerm(wrapped_res, res_logging_sort, op, TermVec{ t1, t2 }));

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
  }

  return res;
}

Term LoggingSolver::make_term(const Op op,
                              const Term & t1,
                              const Term & t2,
                              const Term & t3) const
{
  shared_ptr<LoggingTerm> lt1 = static_pointer_cast<LoggingTerm>(t1);
  shared_ptr<LoggingTerm> lt2 = static_pointer_cast<LoggingTerm>(t2);
  shared_ptr<LoggingTerm> lt3 = static_pointer_cast<LoggingTerm>(t3);
  Term wrapped_res = wrapped_solver->make_term(
      op, lt1->wrapped_term, lt2->wrapped_term, lt3->wrapped_term);
  Sort res_logging_sort =
      compute_sort(op,
                   SortVec{ t1->get_sort(), t2->get_sort(), t3->get_sort() },
                   wrapped_res->get_sort());
  Term res = std::make_shared<LoggingTerm>(
      wrapped_res, res_logging_sort, op, TermVec{ t1, t2, t3 });

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
  }

  return res;
}

Term LoggingSolver::make_term(const Op op, const TermVec & terms) const
{
  TermVec lterms;
  for (auto tt : terms)
  {
    shared_ptr<LoggingTerm> ltt = static_pointer_cast<LoggingTerm>(tt);
    lterms.push_back(ltt->wrapped_term);
  }
  Term wrapped_res = wrapped_solver->make_term(op, lterms);
  SortVec logging_sorts;
  for (auto tt : terms)
  {
    logging_sorts.push_back(tt->get_sort());
  }
  Sort res_logging_sort =
      compute_sort(op, logging_sorts, wrapped_res->get_sort());
  Term res =
      std::make_shared<LoggingTerm>(wrapped_res, res_logging_sort, op, terms);

  // check hash table
  // lookup modifies term in place and returns true if it's a known term
  // i.e. returns existing term and destroying the unnecessary new one
  if (!hashtable->lookup(res))
  {
    // this is the first time this term was created
    hashtable->insert(res);
  }

  return res;
}

Term LoggingSolver::get_value(const Term & t) const
{
  SortKind sk = t->get_sort()->get_sort_kind();
  if (supported_sortkinds_for_get_value.find(sk)
      == supported_sortkinds_for_get_value.end())
  {
    throw NotImplementedException(
        "LoggingSolver does not support get_value for " + smt::to_string(sk));
  }

  shared_ptr<LoggingTerm> lt = static_pointer_cast<LoggingTerm>(t);
  if (t->get_sort()->get_sort_kind() != ARRAY)
  {
    Term wrapped_val = wrapped_solver->get_value(lt->wrapped_term);
    return std::make_shared<LoggingTerm>(
        wrapped_val, t->get_sort(), Op(), TermVec{});
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
    Term res = make_term(out_const_base, t->get_sort());
    for (auto elem : pairs)
    {
      res = make_term(Store, res, elem.first, elem.second);
    }
    return res;
  }
}

TermVec LoggingSolver::get_unsat_core()
{
  TermVec underlying_core = wrapped_solver->get_unsat_core();
  TermVec core;
  for (auto c : underlying_core)
  {
    // assumption: these should be (possible negated) Boolean literals
    // that were used in check_sat_assuming
    // assumption_cache stored a mapping so we can recover the logging term
    if (assumption_cache->find(c) == assumption_cache->end())
    {
      throw InternalSolverException(
          "Got an element in the unsat core that was not cached from "
          "check_sat_assuming in LoggingSolver.");
    }
    Term log_c = assumption_cache->at(c);
    core.push_back(log_c);
  }
  return core;
}

UnorderedTermMap LoggingSolver::get_array_values(const Term & arr,
                                                 Term & out_const_base) const
{
  Sort arrsort = arr->get_sort();
  Sort idxsort = arrsort->get_indexsort();
  Sort elemsort = arrsort->get_elemsort();
  shared_ptr<LoggingTerm> larr = static_pointer_cast<LoggingTerm>(arr);
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
    out_const_base = Term(
        new LoggingTerm(wrapped_out_const_base, elemsort, Op(), TermVec{}));
  }

  Term idx;
  Term val;
  for (auto elem : wrapped_assignments)
  {
    // expecting values in assignment map
    Assert(elem.first->is_value());
    Assert(elem.second->is_value());
    idx = std::make_shared<LoggingTerm>(elem.first, idxsort, Op(), TermVec{});
    val = std::make_shared<LoggingTerm>(elem.second, elemsort, Op(), TermVec{});
    assignments[idx] = val;
  }

  return assignments;
}

void LoggingSolver::reset()
{
  wrapped_solver->reset();
  hashtable->clear();
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
  shared_ptr<LoggingTerm> lt = static_pointer_cast<LoggingTerm>(t);
  wrapped_solver->assert_formula(lt->wrapped_term);
}

Result LoggingSolver::check_sat()
{
  Result r = wrapped_solver->check_sat();
  return r;
}

Result LoggingSolver::check_sat_assuming(const TermVec & assumptions)
{
  // only needs to remember the latest set of assumptions
  assumption_cache->clear();
  TermVec lassumps;
  shared_ptr<LoggingTerm> la;
  for (auto a : assumptions)
  {
    la = static_pointer_cast<LoggingTerm>(a);
    lassumps.push_back(la->wrapped_term);
    // store a mapping from the wrapped term to the logging term
    (*assumption_cache)[la->wrapped_term] = la;
  }
  return wrapped_solver->check_sat_assuming(lassumps);
}

void LoggingSolver::push(uint64_t num) { wrapped_solver->push(num); }

void LoggingSolver::pop(uint64_t num) { wrapped_solver->pop(num); }

void LoggingSolver::reset_assertions() { wrapped_solver->reset_assertions(); }

}  // namespace smt
