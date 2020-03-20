#include "logging_solver.h"

using namespace std;

namespace smt {

/* LoggingSolver */

// implementations

LoggingSolver::LoggingSolver(SmtSolver s) : solver(s) {}

LoggingSolver::~LoggingSolver() {}

Sort LoggingSolver::make_sort(const SortKind sk) const
{
  Sort sort = solver->make_sort(sk);
  Sort loggingsort(new LoggingSort(sk, sort));
  return loggingsort;
}

Sort LoggingSolver::make_sort(const SortKind sk, uint64_t size) const
{
  Sort sort = solver->make_sort(sk, size);
  Sort loggingsort(new LoggingSort(sk, sort));
  return loggingsort;
}

Sort LoggingSort::make_sort(const SortKind sk, const Sort & sort1) const
{
  shared_ptr<LoggingSort> ls1 = static_pointer_cast<LoggingSort>(sort1);
  Sort sort = solver->make_sort(sk, ls1->sort);
  Sort loggingsort(new LoggingSort(sk, sort));
  return loggingsort;
}

Sort LoggingSort::make_sort(const SortKind sk,
                            const Sort & sort1,
                            const Sort & sort2) const
{
  shared_ptr<LoggingSort> ls1 = static_pointer_cast<LoggingSort>(sort1);
  shared_ptr<LoggingSort> ls2 = static_pointer_cast<LoggingSort>(sort2);
  Sort sort = solver->make_sort(sk, ls1->sort, ls2->sort);
  Sort loggingsort(new LoggingSort(sk, sort));
  return loggingsort;
}

Sort LoggingSort::make_sort(const SortKind sk,
                            const Sort & sort1,
                            const Sort & sort2,
                            const Sort & sort3) const
{
  shared_ptr<LoggingSort> ls1 = static_pointer_cast<LoggingSort>(sort1);
  shared_ptr<LoggingSort> ls2 = static_pointer_cast<LoggingSort>(sort2);
  shared_ptr<LoggingSort> ls3 = static_pointer_cast<LoggingSort>(sort3);
  Sort sort = solver->make_sort(sk, ls1->sort, ls2->sort, ls3->sort);
  Sort loggingsort(new LoggingSort(sk, sort));
  return loggingsort;
}

Sort LoggingSort::make_sort(SortKind sk, const SortVec & sorts) const
{
  // convert to sorts stored by LoggingSorts
  SortVec sub_sorts;
  for (auto s : sorts)
  {
    sub_sorts.push_back(static_pointer_cast<LoggingSort>(s)->sort);
  }
  Sort sort = solver->make_sort(sk, sub_sorts);
  Sort loggingsort(new LoggingSort(sk, sort));
  return loggingsort;
}

// dispatched to underlying solver
void LoggingSolver::set_opt(const std::string option, const std::string value)
{
  solver->set_opt(option, value);
}

void LoggingSolver::set_logic(const std::string logic)
{
  solver - set_logic(logic);
}

void LoggingSolver::assert_formula(const Term & t) const
{
  solver->assert_formula(t);
}

Result LoggingSolver::check_sat() { solver->check_sat(t); }

Result LoggingSolver::check_sat_assuming(const TermVec & assumptions)
{
  solver->check_sat_assuming(assumptions);
}

void LoggingSolver::push(uint64_t num = 1) { solver->push(num); }

void LoggingSolver::pop(uint64_t num = 1) { solver->pop(num); }

void LoggingSolver::reset_assertions() { solver->reset_assertions(); }

}  // namespace smt
