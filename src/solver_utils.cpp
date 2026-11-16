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

#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <string>

#include "smt-switch/datatype.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt::backend {

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
