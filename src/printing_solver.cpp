/*********************                                                        */
/*! \file printing_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
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

#include "printing_solver.h"

#include "utils.h"

using namespace std;

namespace smt {

/* PrintingSolver */

// implementations

PrintingSolver::PrintingSolver(SmtSolver s)
    : wrapped_solver(s),
      hashtable(new TermHashTable()),
      assumption_cache(new UnorderedTermMap())
{
}

PrintingSolver::~PrintingSolver() {}

Sort PrintingSolver::make_sort(const string name, uint64_t arity) const
{
  Sort wrapped_sort = wrapped_solver->make_sort(name, arity);
  return wrapped_sort;
}

Sort PrintingSolver::make_sort(const SortKind sk) const
{
  Sort sort = wrapped_solver->make_sort(sk);
  return sort;
}

Sort PrintingSolver::make_sort(const SortKind sk, uint64_t size) const
{
  Sort sort = wrapped_solver->make_sort(sk, size);
  return sort;
}

Sort PrintingSolver::make_sort(const SortKind sk, const Sort & sort1) const
{
  shared_ptr<LoggingSort> ls1 = static_pointer_cast<LoggingSort>(sort1);
  Sort sort = wrapped_solver->make_sort(sk, ls1->wrapped_sort);
  return sort;
}

Sort PrintingSolver::make_sort(const SortKind sk,
                              const Sort & sort1,
                              const Sort & sort2) const
{
  shared_ptr<LoggingSort> ls1 = static_pointer_cast<LoggingSort>(sort1);
  shared_ptr<LoggingSort> ls2 = static_pointer_cast<LoggingSort>(sort2);
  Sort sort =
      wrapped_solver->make_sort(sk, ls1->wrapped_sort, ls2->wrapped_sort);
  return sort;
}

Sort PrintingSolver::make_sort(const SortKind sk,
                              const Sort & sort1,
                              const Sort & sort2,
                              const Sort & sort3) const
{
  shared_ptr<LoggingSort> ls1 = static_pointer_cast<LoggingSort>(sort1);

  shared_ptr<LoggingSort> ls2 = static_pointer_cast<LoggingSort>(sort2);
  shared_ptr<LoggingSort> ls3 = static_pointer_cast<LoggingSort>(sort3);
  Sort sort = wrapped_solver->make_sort(
      sk, ls1->wrapped_sort, ls2->wrapped_sort, ls3->wrapped_sort);
  return sort;
}

Sort PrintingSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  // convert to sorts stored by LoggingSorts
  SortVec sub_sorts;
  for (auto s : sorts)
  {
    sub_sorts.push_back(static_pointer_cast<LoggingSort>(s)->wrapped_sort);
  }
  Sort sort = wrapped_solver->make_sort(sk, sub_sorts);
  return sort;
}


Sort PrintingSolver::make_sort(const DatatypeDecl & d) const {
  throw NotImplementedException("PrintingSolver::make_sort");
};
DatatypeDecl PrintingSolver::make_datatype_decl(const std::string & s)  {
    throw NotImplementedException("PrintingSolver::make_datatype_decl");
}
DatatypeConstructorDecl PrintingSolver::make_datatype_constructor_decl(const std::string s) const {
    throw NotImplementedException("PrintingSolver::make_datatype_constructor_decl");
};
void PrintingSolver::add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const {
  throw NotImplementedException("PrintingSolver::add_constructor");
};
void PrintingSolver::add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const {
  throw NotImplementedException("PrintingSolver::add_selector");
};
void PrintingSolver::add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const {
  throw NotImplementedException("PrintingSolver::add_selector_self");
};

Term PrintingSolver::get_constructor(const Sort & s, std::string name) const  {
  throw NotImplementedException("PrintingSolver::get_constructor");
};
Term PrintingSolver::get_tester(const Sort & s, std::string name) const  {
  throw NotImplementedException("PrintingSolver::get_testeer");
};

Term PrintingSolver::get_selector(const Sort & s, std::string con, std::string name) const  {
  throw NotImplementedException("PrintingSolver::get_selector");
};


Term PrintingSolver::make_term(bool b) const
{
  Term wrapped_res = wrapped_solver->make_term(b);
  return wrapped_res;
}

Term PrintingSolver::make_term(int64_t i, const Sort & sort) const
{
  Term wrapped_res = wrapped_solver->make_term(i, sort);
  return wrapped_res;
}

Term PrintingSolver::make_term(const string name,
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

Term PrintingSolver::make_term(const Term & val, const Sort & sort) const
{
  Term res = wrapped_solver->make_term(val, sort);
  return res;
}

Term PrintingSolver::make_symbol(const string name, const Sort & sort)
{
  Term res = wrapped_solver->make_symbol(name, sort);
  return res;
}

Term PrintingSolver::make_term(const Op op, const Term & t) const
{
  Term res = wrapped_solver->make_term(op, t);
  return res;
}

Term PrintingSolver::make_term(const Op op,
                              const Term & t1,
                              const Term & t2) const
{
  Term res = wrapped_solver->make_term(op, t1, t2);
  return res;
}

Term PrintingSolver::make_term(const Op op,
                              const Term & t1,
                              const Term & t2,
                              const Term & t3) const
{
  Term res = wrapped_solver->make_term(op, t1, t2, t3);
  return res;
}

Term PrintingSolver::make_term(const Op op, const TermVec & terms) const
{
  Term res = wrapped_solver->make_term(op, terms);
  return res;
}

Term PrintingSolver::get_value(const Term & t) const
{
  Term res = wrapped_solver->get_value(t);
  return res;
}

TermVec PrintingSolver::get_unsat_core()
{
  TermVec res = wrapped_solver->get_unsat_core();
  return res;
}


UnorderedTermMap PrintingSolver::get_array_values(const Term & arr,
                                                 Term & out_const_base) const
{
  UnorderedTermMap assignments = wrapped_solver->get_array_values(arr, out_const_base);
  return assignments;
}

void PrintingSolver::reset()
{
  wrapped_solver->reset();
}

// dispatched to underlying solver

void PrintingSolver::set_opt(const std::string option, const std::string value)
{
  wrapped_solver->set_opt(option, value);
}

void PrintingSolver::set_logic(const std::string logic)
{
  wrapped_solver->set_logic(logic);
}

void PrintingSolver::assert_formula(const Term & t)
{
  shared_ptr<LoggingTerm> lt = static_pointer_cast<LoggingTerm>(t);
  wrapped_solver->assert_formula(lt->wrapped_term);
}

Result PrintingSolver::check_sat() { return wrapped_solver->check_sat(); }

Result PrintingSolver::check_sat_assuming(const TermVec & assumptions)
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

void PrintingSolver::push(uint64_t num) { wrapped_solver->push(num); }

void PrintingSolver::pop(uint64_t num) { wrapped_solver->pop(num); }

void PrintingSolver::reset_assertions() { wrapped_solver->reset_assertions(); }

}  // namespace smt
