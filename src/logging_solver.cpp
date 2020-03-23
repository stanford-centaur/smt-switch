#include "logging_solver.h"
#include "logging_sort.h"
#include "logging_sort_computation.h"
#include "logging_term.h"

using namespace std;

namespace smt {

/* LoggingSolver */

// implementations

LoggingSolver::LoggingSolver(SmtSolver s)
    : solver(s), hashtable(new TermHashTable())
{
}

LoggingSolver::~LoggingSolver() {}

Sort LoggingSolver::make_sort(const string name, uint64_t arity) const
{
  Sort wrapped_sort = solver->make_sort(name, arity);
  return make_logging_sort(name, arity);
}

Sort LoggingSolver::make_sort(const SortKind sk) const
{
  Sort sort = solver->make_sort(sk);
  return make_logging_sort(sk, sort);
}

Sort LoggingSolver::make_sort(const SortKind sk, uint64_t size) const
{
  Sort sort = solver->make_sort(sk, size);
  return make_logging_sort(sk, sort);
}

Sort LoggingSolver::make_sort(const SortKind sk, const Sort & sort1) const
{
  shared_ptr<LoggingSort> ls1 = static_pointer_cast<LoggingSort>(sort1);
  Sort sort = solver->make_sort(sk, ls1->sort);
  return make_logging_sort(sk, sort, sort1);
}

Sort LoggingSolver::make_sort(const SortKind sk,
                              const Sort & sort1,
                              const Sort & sort2) const
{
  shared_ptr<LoggingSort> ls1 = static_pointer_cast<LoggingSort>(sort1);
  shared_ptr<LoggingSort> ls2 = static_pointer_cast<LoggingSort>(sort2);
  Sort sort = solver->make_sort(sk, ls1->sort, ls2->sort);
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
  Sort sort = solver->make_sort(sk, ls1->sort, ls2->sort, ls3->sort);
  return make_logging_sort(sk, sort, sort1, sort2, sort3);
}

Sort LoggingSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  // convert to sorts stored by LoggingSorts
  SortVec sub_sorts;
  for (auto s : sorts)
  {
    sub_sorts.push_back(static_pointer_cast<LoggingSort>(s)->sort);
  }
  Sort sort = solver->make_sort(sk, sub_sorts);
  return make_logging_sort(sk, sort, sorts);
}

Term LoggingSolver::make_term(bool b) const
{
  Term wrapped_res = solver->make_term(b);
  Sort boolsort = make_logging_sort(BOOL, wrapped_res->get_sort());
  Term res(new LoggingTerm(wrapped_res, boolsort, Op(), TermVec{}));

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
  Term wrapped_res = solver->make_term(i, lsort->sort);
  Term res(new LoggingTerm(wrapped_res, sort, Op(), TermVec{}));

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
  Term wrapped_res = solver->make_term(name, lsort->sort, base);
  Term res(new LoggingTerm(wrapped_res, sort, Op(), TermVec{}));

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
  shared_ptr<LoggingSort> lsort = static_pointer_cast<LoggingSort>(sort);
  Term wrapped_res = solver->make_term(val, lsort->sort);
  Term res(new LoggingTerm(wrapped_res, sort, Op(), TermVec{}));

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
  Term wrapped_sym = solver->make_term(name, lsort->sort);
  Term res(new LoggingTerm(wrapped_sym, sort, Op(), TermVec{}));

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
  Term wrapped_res = solver->make_term(op, lt->term);
  Sort res_logging_sort =
      compute_sort(op, SortVec{ t->get_sort() }, wrapped_res->get_sort());
  Term res(new LoggingTerm(wrapped_res, res_logging_sort, op, TermVec{ t }));

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
  Term wrapped_res = solver->make_term(op, lt1, lt2);
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
  Term wrapped_res = solver->make_term(op, lt1->term, lt2->term, lt3->term);
  Sort res_logging_sort =
      compute_sort(op,
                   SortVec{ t1->get_sort(), t2->get_sort(), t3->get_sort() },
                   wrapped_res->get_sort());
  Term res(new LoggingTerm(
      wrapped_res, res_logging_sort, op, TermVec{ t1, t2, t3 }));

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
    lterms.push_back(ltt->term);
  }
  Term wrapped_res = solver->make_term(op, lterms);
  SortVec logging_sorts;
  for (auto tt : terms)
  {
    logging_sorts.push_back(tt->get_sort());
  }
  Sort res_logging_sort =
      compute_sort(op, logging_sorts, wrapped_res->get_sort());
  Term res(new LoggingTerm(wrapped_res, res_logging_sort, op, terms));

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

Term LoggingSolver::get_value(Term & t) const
{
  shared_ptr<LoggingTerm> lt = static_pointer_cast<LoggingTerm>(t);
  Term wrapped_val = solver->get_value(lt->term);
  Term val(new LoggingTerm(wrapped_val, t->get_sort(), Op(), TermVec{}));
  return val;
}

void LoggingSolver::reset()
{
  solver->reset();
  hashtable->clear();
}

// dispatched to underlying solver

void LoggingSolver::set_opt(const std::string option, const std::string value)
{
  solver->set_opt(option, value);
}

void LoggingSolver::set_logic(const std::string logic)
{
  solver->set_logic(logic);
}

void LoggingSolver::assert_formula(const Term & t) const
{
  solver->assert_formula(t);
}

Result LoggingSolver::check_sat() { return solver->check_sat(); }

Result LoggingSolver::check_sat_assuming(const TermVec & assumptions)
{
  return solver->check_sat_assuming(assumptions);
}

void LoggingSolver::push(uint64_t num) { solver->push(num); }

void LoggingSolver::pop(uint64_t num) { solver->pop(num); }

void LoggingSolver::reset_assertions() { solver->reset_assertions(); }

}  // namespace smt
