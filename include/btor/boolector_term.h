#ifndef BOOLECTOR_TERM_H
#define BOOLECTOR_TERM_H

#include <vector>
#include <iostream>

#include "boolector/boolector.h"
#include "term.h"
#include "ops.h"

// TODO: Figure out if we should have extern C here?
//       seems to be working already

namespace smt {

class BoolectorTerm : public AbsTerm
{
 public:
 BoolectorTerm(Btor* b, BoolectorNode* n,
               std::vector<std::shared_ptr<AbsTerm>> c,
               Op o)
   : btor(b), node(n), children(c), op(o)
    {};
  ~BoolectorTerm()
  {
    boolector_release(btor, node);
  }
  // TODO: check if this is okay -- probably not
  std::size_t hash() const override { return (std::size_t) boolector_get_node_id(btor, node); };
  bool compare(const std::shared_ptr<AbsTerm>& absterm) const override
  {
    BoolectorTerm* other = static_cast<BoolectorTerm*>(absterm.get());
    return boolector_get_node_id(this->btor, this->node) == boolector_get_node_id(other->btor, other->node);
  }
  std::vector<std::shared_ptr<AbsTerm>> get_children() const override
  {
    return children;
  }
  Op get_op() const override { return op; };
  std::shared_ptr<AbsSort> get_sort() const override
  {
    throw NotImplementedException("Can't get sort from btor");
  }
  virtual std::string to_string() const override
  {
    throw NotImplementedException("Can't get string representation from btor");
  }
 private:
  Btor * btor;
  BoolectorNode * node;
  std::vector<std::shared_ptr<AbsTerm>> children;
  Op op;
};

}

#endif
