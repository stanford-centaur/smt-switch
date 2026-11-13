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

#include <cstdint>
#include <string>
#include <vector>

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

msat_term ext_msat_make_negate(msat_env e, msat_term t);
msat_term ext_msat_make_abs(msat_env e, msat_term t);
msat_term ext_msat_make_intdiv(msat_env e, msat_term t1, msat_term t2);
msat_term ext_msat_make_divisible(msat_env e, std::uint64_t n, msat_term t);
msat_term ext_msat_make_nop(msat_env e, msat_term t);
msat_term ext_msat_is_int(msat_env e, msat_term t);
msat_term ext_msat_make_xor(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_implies(msat_env e, msat_term t0, msat_term t1);
// mathsat doesn't support ites where the branch terms are bools
// this rewrites that case so we can support it in smt-switch
msat_term ext_msat_make_ite(msat_env e, msat_term i, msat_term t, msat_term el);
msat_term ext_msat_make_distinct(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_minus(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_lt(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_gt(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_geq(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_mod(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_pow(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_nand(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_nor(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_xnor(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_smod(msat_env e, msat_term s, msat_term t);
msat_term ext_msat_make_bv_ugt(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_ugeq(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_sgt(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_sgeq(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_uf(msat_env e,
                           msat_decl func,
                           std::vector<msat_term> args);

}  // namespace smt

#endif  // SMT_SWITCH_MSAT_EXTENSIONS_H
