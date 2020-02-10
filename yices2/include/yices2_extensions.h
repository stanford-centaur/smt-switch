#ifndef SMT_YICES2_EXTENSIONS_H
#define SMT_YICES2_EXTENSIONS_H

#include <gmp.h>
#include "yices.h"

namespace smt {

term_t ext_yices_select(term_t arr, term_t idx);
term_t ext_yices_make_bv_number(const char * val, size_t size, int base);

}  // namespace smt

#endif
