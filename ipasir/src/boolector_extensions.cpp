/*********************                                                        */
/*! \file boolector_extensions.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Helper functions for certain operations in Boolector C API
**
**
**/

#include "math.h"

#include "boolector_extensions.h"

namespace smt {
BoolectorNode * custom_boolector_rotate_left(Btor * btor,
                                             BoolectorNode * node,
                                             uint32_t n)
{
  uint32_t width = boolector_get_width(btor, node);
  if ((n == 0) || (width == 1))
  {
    return boolector_uext(btor, node, 0);
  }

  // compute directly with extracts
  BoolectorNode * top_slice = boolector_slice(btor, node, width - 1, width - n);
  BoolectorNode * bot_slice = boolector_slice(btor, node, width - n - 1, 0);
  BoolectorNode * res = boolector_concat(btor, bot_slice, top_slice);
  boolector_release(btor, top_slice);
  boolector_release(btor, bot_slice);
  return res;
}

BoolectorNode * custom_boolector_rotate_right(Btor * btor,
                                              BoolectorNode * node,
                                              uint32_t n)
{
  uint32_t width = boolector_get_width(btor, node);
  if ((n == 0) || (width == 1))
  {
    return boolector_uext(btor, node, 0);
  }

  // compute directly with extracts
  BoolectorNode * top_slice = boolector_slice(btor, node, width - 1, n);
  BoolectorNode * bot_slice = boolector_slice(btor, node, n - 1, 0);
  BoolectorNode * res = boolector_concat(btor, bot_slice, top_slice);
  boolector_release(btor, top_slice);
  boolector_release(btor, bot_slice);
  return res;
}
}  // namespace smt
