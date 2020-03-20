#include "logging_solver.h"
#include "logging_sort.h"
#include "logging_term.h"

using namespace std;

namespace smt {

/* LoggingSolver */

// implementations

LoggingSolver::LoggingSolver(SmtSolver s) : solver(s) {}

LoggingSolver::~LoggingSolver() {}

// TODO: Fix these -- need to create the right kind of LoggingSort
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
