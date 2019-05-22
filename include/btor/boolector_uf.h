#ifndef SMT_BOOLECTOR_UF_H
#define SMT_BOOLECTOR_UF_H

#include <memory>
#include <utility>
#include <vector>

#include "uf.h"

#include "boolector/boolector.h"

namespace smt {
class BoolectorUF : public AbsUF {
public:
  BoolectorUF(Btor *b, BoolectorNode *n, unsigned int a, Sort s)
    : AbsUF(a), btor(b), node(n), sort(s){};
  Sort get_sort() const override { return sort; };
  BoolectorNode * get_boolector_node() { return node; };
protected:
  Btor *btor;
  BoolectorNode *node;
  // Specifically this should be a function sort
  Sort sort;

  friend class BoolectorSolver;
};
} // namespace smt

#endif
