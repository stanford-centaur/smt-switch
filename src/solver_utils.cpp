/*!
 * \file solver_utils.cpp
 * \brief Utility functions for solver implementations
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/solver_utils.h"

#include <fcntl.h>
#include <unistd.h>

#include <algorithm>
#include <cerrno>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "smt-switch/datatype.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt::backend {

Term make_nary_term(const AbsSmtSolver * solver,
                    const Op & op,
                    const TermVec & terms)
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
      res = solver->make_term(op, res, terms[i]);
    }
    return res;
  }
  else if (is_right_assoc(op.prim_op))
  {
    Term res = terms[size - 1];
    for (std::size_t i = 1; i < size; ++i)
    {
      res = solver->make_term(op, terms[size - 1 - i], res);
    }
    return res;
  }

  TermVec conjuncts;
  if (is_chainable(op.prim_op))
  {
    for (std::size_t i = 0; i + 1 < size; ++i)
    {
      conjuncts.push_back(solver->make_term(op, terms[i], terms[i + 1]));
    }
  }
  else if (is_pairwise(op.prim_op))
  {
    for (std::size_t i = 0; i < size; ++i)
    {
      for (std::size_t j = i + 1; j < size; ++j)
      {
        conjuncts.push_back(solver->make_term(op, terms[i], terms[j]));
      }
    }
  }
  else
  {
    throw IncorrectUsageException("Can't apply " + op.to_string() + " to "
                                  + std::to_string(size) + " terms.");
  }
  return conjuncts.size() == 1 ? conjuncts[0]
                               : solver->make_term(And, conjuncts);
}

void check_quantifier_binders(const Op & op, const TermVec & terms)
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

std::uint32_t narrow_index(const Op & op, std::uint64_t idx)
{
  if (!fits_in<std::uint32_t>(idx))
  {
    throw IncorrectUsageException("Index " + std::to_string(idx) + " of "
                                  + op.to_string()
                                  + " does not fit in the 32 bits this solver "
                                    "accepts");
  }
  return static_cast<std::uint32_t>(idx);
}

std::uint32_t narrow_width(std::uint64_t width)
{
  return narrow<std::uint32_t>(width, "a bit-vector width");
}

std::uint32_t narrow_levels(std::uint64_t levels)
{
  return narrow<std::uint32_t>(levels, "a number of levels");
}

std::uint32_t narrow_num_args(std::size_t num_args)
{
  return narrow<std::uint32_t>(num_args, "a number of arguments");
}

bool bool_option_value(const std::string & option, const std::string & value)
{
  if (value != "true" && value != "false")
  {
    throw IncorrectUsageException("The option " + option
                                  + " takes true or false, not " + value);
  }
  return value == "true";
}

double time_limit_seconds(const std::string & value)
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
  return std::min(seconds, longest);
}

std::uint64_t time_limit_milliseconds(const std::string & value)
{
  // time_limit_seconds keeps the limit far below 2^64 milliseconds.
  return static_cast<std::uint64_t>(time_limit_seconds(value) * 1000);
}

UnorderedTermMap store_chain_values(
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

int make_cloexec_pipe(int (&fds)[2])
{
  // pipe2 would set the flag in the same call, but macOS lacks it.
  if (pipe(fds) != 0)
  {
    fds[0] = -1;
    fds[1] = -1;
    return errno;
  }
  for (int fd : fds)
  {
    if (fcntl(fd, F_SETFD, FD_CLOEXEC) != 0)
    {
      int fcntl_errno = errno;
      close(fds[0]);
      close(fds[1]);
      fds[0] = -1;
      fds[1] = -1;
      return fcntl_errno;
    }
  }
  return 0;
}

void throw_foreign_pointer(const Term & h)
{
  throw IncorrectUsageException("Term " + h->to_string()
                                + " was made by another solver");
}

void throw_foreign_pointer(const Sort & h)
{
  throw IncorrectUsageException("Sort " + h->to_string()
                                + " was made by another solver");
}

void throw_foreign_pointer(const DatatypeDecl & h)
{
  throw IncorrectUsageException("Datatype declaration " + h->get_name()
                                + " was made by another solver");
}

void throw_foreign_pointer(const DatatypeConstructorDecl & h)
{
  throw IncorrectUsageException("Datatype constructor declaration "
                                + h->get_name()
                                + " was made by another solver");
}

void throw_foreign_pointer(const Datatype & h)
{
  throw IncorrectUsageException("Datatype " + h->get_name()
                                + " was made by another solver");
}

std::string internal_name(const std::string & kind, std::uint64_t index)
{
  return std::string(INTERNAL_NAME_PREFIX) + kind + "_" + std::to_string(index);
}

bool is_internal_name(std::string_view name)
{
  return name.compare(0, INTERNAL_NAME_PREFIX.size(), INTERNAL_NAME_PREFIX)
         == 0;
}

}  // namespace smt::backend
