/*!
 * \file msat_extensions.h
 * \brief Helper functions for certain operations in MathSAT C API
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_MSAT_EXTENSIONS_H
#define SMT_SWITCH_MSAT_EXTENSIONS_H

#include <mathsat.h>

#include <string>

namespace smt {

namespace detail {

/** Frees memory a MathSAT call returned, through msat_free */
struct MsatFreeDeleter
{
  void operator()(void * p) const;
};

/** Copies and frees a string a MathSAT call returned
 *  @param s the string, or null if the call failed
 *  @throws SolverException if s is null
 */
std::string get_msat_string(char * s);

/** The name MathSAT gives an option smt-switch names differently, or the
 *  option itself
 */
std::string msat_option_name(const std::string & option);

/** The last error message MathSAT reported in e, empty if there is none
 *  MathSAT keeps a message until the next error replaces it, also across
 *  successful calls, and does not say whether a call set it. It set one for
 *  every unknown result seen so far, terminations included, so an unknown
 *  result is explained by this message.
 */
std::string last_error_message(msat_env e);

}  // namespace detail

}  // namespace smt

#endif  // SMT_SWITCH_MSAT_EXTENSIONS_H
