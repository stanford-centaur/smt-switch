/*!
 * \file yices2_extensions.h
 * \brief Helper functions for certain operations in the Yices C API
 * \author Amalee Wilson
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_YICES2_EXTENSIONS_H
#define SMT_SWITCH_YICES2_EXTENSIONS_H

#include <yices_types.h>

#include <memory>
#include <string>

namespace smt {

namespace detail {

struct Yices2ModelDeleter
{
  void operator()(model_t * model) const;
};

/** A model from yices_get_model, freed with yices_free_model */
using Yices2ModelPtr = std::unique_ptr<model_t, Yices2ModelDeleter>;

/** Yices' description of its last error, freeing the string it returns and
 *  clearing the error, which later calls would otherwise report again
 */
std::string get_yices2_error();

/** Copies and frees a string a Yices call returned
 *  @param s the string, or null if the call failed
 *  @throws SolverException with Yices' error if s is null
 */
std::string get_yices2_string(char * s);

}  // namespace detail

term_t ext_yices_select(term_t arr, term_t idx);
term_t ext_yices_store(term_t arr, term_t idx, term_t nu);
term_t ext_yices_bvcomp(term_t t0, term_t t1);
term_t ext_yices_bvxor3(term_t t0, term_t t1, term_t t2);

}  // namespace smt

#endif  // SMT_SWITCH_YICES2_EXTENSIONS_H
