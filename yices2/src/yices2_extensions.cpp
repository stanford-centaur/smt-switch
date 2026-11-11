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

#include "yices2_extensions.h"

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <yices.h>

#include <string>

using namespace std;

namespace smt {

string take_yices_error()
{
  char * reason = yices_error_string();
  string msg(reason);
  yices_free_string(reason);
  yices_clear_error();
  // Yices2 ends a few of its error messages with a newline.
  if (!msg.empty() && msg.back() == '\n')
  {
    msg.pop_back();
  }
  return msg;
}

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

term_t ext_yices_bvcomp(term_t t0, term_t t1)
{
  // ite(t0 == t1, #b1, #b0)
  return yices_ite(
      yices_eq(t0, t1), yices_bvconst_int64(1, 1), yices_bvconst_int64(1, 0));
}

term_t ext_yices_bvxor3(term_t t0, term_t t1, term_t t2)
{
#if __YICES_VERSION > 2 || __YICES_VERSION_MAJOR > 6 \
    || __YICES_VERSION_PATCHLEVEL >= 3
  return yices_bvxor3(t0, t1, t2);
#else
  // Before 2.6.3, yices_bvxor3 computes a bvor.
  return yices_bvxor2(yices_bvxor2(t0, t1), t2);
#endif
}

}  // namespace smt

#endif
