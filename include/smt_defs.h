#ifndef SMT_DEFS_H
#define SMT_DEFS_H

#include <memory>

namespace smt {

struct Op;

class AbsSort;
using Sort = std::shared_ptr<AbsSort>;

class AbsTerm;
using Term = std::shared_ptr<AbsTerm>;

class AbsSmtSolver;
using SmtSolver = std::unique_ptr<AbsSmtSolver>;

}  // namespace smt

#endif
