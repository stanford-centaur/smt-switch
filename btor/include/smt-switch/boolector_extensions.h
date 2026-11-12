/*!
 * \file boolector_extensions.h
 * \brief Helper functions for certain operations in Boolector C API
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_BOOLECTOR_EXTENSIONS_H
#define SMT_SWITCH_BOOLECTOR_EXTENSIONS_H

#include <btortypes.h>

#include <cstdint>

namespace smt {
BoolectorNode * custom_boolector_rotate_left(Btor * btor,
                                             BoolectorNode * node,
                                             uint32_t n);

BoolectorNode * custom_boolector_rotate_right(Btor * btor,
                                              BoolectorNode * node,
                                              uint32_t n);
}  // namespace smt

#endif  // SMT_SWITCH_BOOLECTOR_EXTENSIONS_H
