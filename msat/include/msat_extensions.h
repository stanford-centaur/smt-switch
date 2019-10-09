#ifndef SMT_MSAT_EXTENSIONS_H
#define SMT_MSAT_EXTENSIONS_H

#include "mathsat.h"

namespace smt {
msat_term ext_msat_make_negate(msat_env e, msat_term t);
msat_term ext_msat_make_abs(msat_env e, msat_term t);
msat_term ext_msat_make_nop(msat_env e, msat_term t);
msat_term ext_msat_is_int(msat_env e, msat_term t);
msat_term ext_msat_make_xor(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_implies(msat_env e, msat_term t0, msat_term t1);
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
}  // namespace smt

#endif
