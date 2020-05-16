/*********************                                                        */
/*! \file boolector_extensions.h
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

#ifndef SMT_BOOLECTOR_EXTENSIONS_H
#define SMT_BOOLECTOR_EXTENSIONS_H

#include "boolector.h"

namespace smt {
BoolectorNode * custom_boolector_rotate_left(Btor * btor,
                                             BoolectorNode * node,
                                             uint32_t n);

BoolectorNode * custom_boolector_rotate_right(Btor * btor,
                                              BoolectorNode * node,
                                              uint32_t n);
}  // namespace smt

#endif
