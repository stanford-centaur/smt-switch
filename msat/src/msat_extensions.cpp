/*!
 * \file msat_extensions.cpp
 * \brief Helper functions for certain operations in MathSAT C API
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/msat_extensions.h"

#include <mathsat.h>

#include <memory>
#include <string>

#include "smt-switch/exceptions.h"

namespace smt {

void detail::MsatFreeDeleter::operator()(void * p) const { msat_free(p); }

std::string detail::get_msat_string(char * s)
{
  std::unique_ptr<char, MsatFreeDeleter> owned(s);
  if (!owned)
  {
    throw SolverException("MathSAT failed to print a term or sort");
  }
  return owned.get();
}

std::string detail::msat_option_name(const std::string & option)
{
  if (option == "produce-interpolants")
  {
    return "interpolation";
  }
  if (option == "produce-models")
  {
    return "model_generation";
  }
  return option;
}

std::string detail::last_error_message(msat_env e)
{
  const char * msg = msat_last_error_message(e);
  return msg ? msg : "";
}

}  // namespace smt
