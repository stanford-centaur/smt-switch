#ifndef SMT_DEFS_H
#define SMT_DEFS_H

#include <memory>

namespace smt {

class AbsSort;
using Sort = std::shared_ptr<AbsSort>;
class AbsFun;
using Fun = std::shared_ptr<AbsFun>;
class AbsTerm;
using Term = std::shared_ptr<AbsTerm>;
class Op;

}  // namespace smt

#endif
