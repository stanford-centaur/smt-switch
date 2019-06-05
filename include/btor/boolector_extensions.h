#ifndef SMT_BOOLECTOR_EXTENSIONS_H
#define SMT_BOOLECTOR_EXTENSIONS_H

#include "boolector/boolector.h"

namespace smt {
BoolectorNode * custom_boolector_rotate_left(Btor * btor,
                                             BoolectorNode * node,
                                             uint32_t n);

BoolectorNode * custom_boolector_rotate_right(Btor * btor,
                                              BoolectorNode * node,
                                              uint32_t n);
}  // namespace smt

#endif
