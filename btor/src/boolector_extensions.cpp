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

#include "smt-switch/boolector_extensions.h"

#include <boolector.h>

#include <cstdint>

namespace smt {

namespace {

/** A node held for a scope, and released when the scope ends */
struct ScopedNode
{
  Btor * btor;
  BoolectorNode * node;
  ~ScopedNode() { boolector_release(btor, node); }
};

}  // namespace

BoolectorNode * custom_boolector_rotate_left(Btor * btor,
                                             BoolectorNode * node,
                                             uint32_t n)
{
  uint32_t width = boolector_get_width(btor, node);
  n %= width;
  if (n == 0)
  {
    return boolector_uext(btor, node, 0);
  }

  // compute directly with extracts
  ScopedNode top_slice{ btor,
                        boolector_slice(btor, node, width - 1, width - n) };
  ScopedNode bot_slice{ btor, boolector_slice(btor, node, width - n - 1, 0) };
  return boolector_concat(btor, bot_slice.node, top_slice.node);
}

BoolectorNode * custom_boolector_rotate_right(Btor * btor,
                                              BoolectorNode * node,
                                              uint32_t n)
{
  uint32_t width = boolector_get_width(btor, node);
  n %= width;
  if (n == 0)
  {
    return boolector_uext(btor, node, 0);
  }

  // compute directly with extracts
  ScopedNode top_slice{ btor, boolector_slice(btor, node, width - 1, n) };
  ScopedNode bot_slice{ btor, boolector_slice(btor, node, n - 1, 0) };
  return boolector_concat(btor, bot_slice.node, top_slice.node);
}
}  // namespace smt
