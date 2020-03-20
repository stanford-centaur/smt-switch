#include "logging_solver.h"

using namespace std;

namespace smt {

/* LoggingSolver */

// implementations

LoggingSolver::LoggingSolver(SmtSolver s) : solver(s) {}

LoggingSolver::~LoggingSolver() {}

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
