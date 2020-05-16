/*********************                                                        */
/*! \file yices2_extensions.h
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

#include <gmp.h>
#include "yices.h"

namespace smt {

term_t ext_yices_select(term_t arr, term_t idx);
term_t ext_yices_store(term_t arr, term_t idx, term_t nu);
term_t ext_yices_make_bv_number(const char * val, size_t size, int base);

}  // namespace smt

#endif
