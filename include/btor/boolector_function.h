#ifndef SMT_BOOLECTOR_FUNCTION_H
#define SMT_BOOLECTOR_FUNCTION_H

#include <memory>
#include <utility>
#include <vector>

#include "function.h"
#include "ops.h"

#include "boolector/boolector.h"

namespace smt {
class BoolectorFunction : public AbsFunction {
public:
  BoolectorFunction(Btor *b, BoolectorNode *n, unsigned int a, Sort s)
    : AbsFunction(a), btor(b), node(n), sort(s){};
  Sort get_sort() const override { return sort; };
  BoolectorNode * get_boolector_node() { return node; };
protected:
  Btor *btor;
  BoolectorNode *node;
  // Specifically this should be a function sort
  Sort sort;
};
} // namespace smt

#endif
