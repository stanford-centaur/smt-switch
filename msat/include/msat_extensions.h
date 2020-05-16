/*********************                                                        */
/*! \file msat_extensions.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Helper functions for certain operations in MathSAT C API
**
**
**/

#ifndef SMT_MSAT_EXTENSIONS_H
#define SMT_MSAT_EXTENSIONS_H

#include "mathsat.h"

namespace smt {
msat_term ext_msat_make_negate(msat_env e, msat_term t);
msat_term ext_msat_make_abs(msat_env e, msat_term t);
msat_term ext_msat_make_intdiv(msat_env e, msat_term t1, msat_term t2);
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
msat_term ext_msat_make_bv_nand(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_nor(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_xnor(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_smod(msat_env e, msat_term s, msat_term t);
msat_term ext_msat_make_bv_ugt(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_ugeq(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_sgt(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_sgeq(msat_env e, msat_term t0, msat_term t1);
msat_term ext_msat_make_bv_number(msat_env e,
                                  const char * val,
                                  size_t size,
                                  int base);
msat_term ext_msat_make_uf(msat_env e,
                           msat_decl func,
                           std::vector<msat_term> args);

}  // namespace smt

#endif
