/*********************                                                        */
/*! \file yices2_extensions.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Helper functions for certain operations in the Yices C API
**
**
**/

#ifndef SMT_YICES2_EXTENSIONS_H
#define SMT_YICES2_EXTENSIONS_H

#include <inttypes.h>
#include "gmp.h"
#include "yices.h"
#include "yices2_solver.h"

using namespace std;

namespace smt {

term_t ext_yices_select(term_t arr, term_t idx)
{
  term_t selection = yices_application1(arr, idx);
  return selection;
}

term_t ext_yices_store(term_t arr, term_t idx, term_t nu)
{
  term_t updated = yices_update1(arr, idx, nu);
  return updated;
}

term_t ext_yices_make_bv_number(const char * val, size_t size, int base)
{
  // gmp should be included because it's a dependency of yices
  mpz_t yval;
  mpz_init(yval);
  int status = mpz_set_str(yval, val, base);

  if (status != 0)
  {
    std::string msg("Could not create bv from ");
    msg += val;
    throw IncorrectUsageException(msg);
  }

  term_t res;

  // mpz_t values for bounds checking
  mpz_t exclusive_upper_bnd;
  mpz_init(exclusive_upper_bnd);
  mpz_ui_pow_ui(exclusive_upper_bnd, 2, size);

  if (mpz_sgn(yval) < 0)
  {
    // for overflow checking
    mpz_t tmp;
    mpz_init(tmp);
    mpz_t lower_bnd;
    mpz_init(lower_bnd);

    mpz_ui_pow_ui(tmp, 2, size - 1);
    mpz_neg(lower_bnd, tmp);

    if (mpz_cmp(yval, lower_bnd) < 0)
    {
      std::string msg("Can't represent ");
      msg += val;
      msg += " in " + std::to_string(size) + " bits.";
      mpz_clear(lower_bnd);
      mpz_clear(tmp);
      mpz_clear(exclusive_upper_bnd);
      mpz_clear(yval);
      throw IncorrectUsageException(msg);
    }

    mpz_t negval;
    mpz_init(negval);
    mpz_neg(negval, yval);
    // const mpz_t nv = negval;
    res = yices_bvconst_mpz(size, negval);
    if (res == -1)
    {
      std::string msg("Error creating bit-vector from ");
      msg += val;
      mpz_clear(negval);
      mpz_clear(lower_bnd);
      mpz_clear(tmp);
      mpz_clear(exclusive_upper_bnd);
      mpz_clear(yval);
      throw IncorrectUsageException(msg);
    }
    res = yices_bvneg(res);
    mpz_clear(negval);
    mpz_clear(lower_bnd);
    mpz_clear(tmp);
  }
  else
  {
    if (mpz_cmp(yval, exclusive_upper_bnd) >= 0)
    {
      std::string msg("Can't represent ");
      msg += val;
      msg += " in " + std::to_string(size) + " bits.";
      mpz_clear(exclusive_upper_bnd);
      mpz_clear(yval);
      throw IncorrectUsageException(msg);
    }
    res = yices_bvconst_mpz(size, yval);
  }

  mpz_clear(exclusive_upper_bnd);
  mpz_clear(yval);

  if (res == -1)
  {
    std::string msg("Error creating bit-vector from ");
    msg += val;
    throw IncorrectUsageException(msg);
  }

  return res;
}

}  // namespace smt

#endif
