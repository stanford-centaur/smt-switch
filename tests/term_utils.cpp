/*!
 * \file term_utils.cpp
 * \brief What a term has to match after a round trip through a solver.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "term_utils.h"

#include <cstdint>
#include <string>

#include "utils.h"

using namespace smt;

namespace smt_tests {

namespace {

/** How many values the sort holds, or 0 if it holds infinitely many. */
uint64_t domain_size(const Sort & sort)
{
  switch (sort->get_sort_kind())
  {
    case BOOL: return 2;
    // a wide vector is far past anything worth enumerating, and a width of
    // 64 or more would not fit the count below
    case BV:
      return sort->get_width() < 32 ? uint64_t(1) << sort->get_width() : 0;
    default: return 0;
  }
}

/** The product of the symbols' domain sizes, or 0 when some sort is infinite
 *  or the product exceeds `cap` and is not worth walking.
 */
uint64_t assignment_count(const TermVec & symbols, uint64_t cap)
{
  uint64_t total = 1;
  for (const Term & symbol : symbols)
  {
    uint64_t size = domain_size(symbol->get_sort());
    if (size == 0 || total > cap / size)
    {
      return 0;
    }
    total *= size;
  }
  return total;
}

/** The `index`th assignment, counting each symbol's values in turn. */
UnorderedTermMap assignment(const SmtSolver & solver,
                            const TermVec & symbols,
                            uint64_t index)
{
  UnorderedTermMap values;
  for (const Term & symbol : symbols)
  {
    Sort sort = symbol->get_sort();
    uint64_t size = domain_size(sort);
    uint64_t value = index % size;
    index /= size;
    values[symbol] = sort->get_sort_kind() == BOOL
                         ? solver->make_term(value != 0)
                         : solver->make_term(value, sort);
  }
  return values;
}

}  // namespace

::testing::AssertionResult round_trip_matches(
    const SolverConfiguration & config,
    const SmtSolver & solver,
    const Term & read_back,
    const Term & original)
{
  if (read_back == original)
  {
    return ::testing::AssertionSuccess();
  }

  if (config.is_logging_solver)
  {
    return ::testing::AssertionFailure()
           << "a logging solver records the term it was given, so it had to "
              "come back unchanged\n  put in:   "
           << original << "\n  got back: " << read_back;
  }

  UnorderedTermSet symbol_set;
  get_free_symbolic_consts(original, symbol_set);
  get_free_symbolic_consts(read_back, symbol_set);
  TermVec symbols(symbol_set.begin(), symbol_set.end());

  constexpr uint64_t cap = 1024;
  uint64_t count = symbols.empty() ? 0 : assignment_count(symbols, cap);
  for (uint64_t i = 0; i < count; i++)
  {
    UnorderedTermMap values = assignment(solver, symbols, i);
    Term got = solver->substitute(read_back, values);
    Term want = solver->substitute(original, values);
    if (!got->is_value() || !want->is_value())
    {
      // this solver does not fold a ground term, so ask it instead
      count = 0;
      break;
    }
    if (got != want)
    {
      std::string where;
      for (const auto & entry : values)
      {
        where +=
            " " + entry.first->to_string() + "=" + entry.second->to_string();
      }
      return ::testing::AssertionFailure()
             << "the terms are not equivalent\n  put in:   " << original
             << " = " << want << "\n  got back: " << read_back << " = " << got
             << "\n  under" << where;
    }
  }
  if (count > 0)
  {
    return ::testing::AssertionSuccess();
  }

  // only it knows what it rewrote the term into
  solver->assert_formula(solver->make_term(Distinct, read_back, original));
  if (solver->check_sat().is_unsat())
  {
    return ::testing::AssertionSuccess();
  }
  return ::testing::AssertionFailure()
         << "the solver does not make the terms equal\n  put in:   " << original
         << "\n  got back: " << read_back;
}

}  // namespace smt_tests
