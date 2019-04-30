#ifndef BOOLECTOR_TERM_H
#define BOOLECTOR_TERM_H

#include <vector>

#include "boolector/boolector.h"
#include "term.h"
#include "op.h"

extern "C"
{
  BoolectorNode* boolector_copy(Btor*, BoolectorNode*);
  void boolector_release(Btor*, BoolectorNode*);
}

namespace smt {

class BoolectorTerm : public TermAbs
{
 public:
 BoolectorTerm(Btor* b, BoolectorNode* n,
               std::vector<shared_ptr<BoolectorTerm>> c,
               Op o)
   : btor(b), node(n), children(c), op(o)
    {};
  ~BoolectorTerm()
  {
    boolector_release(btor, node);
  }
  // TODO: check if this is okay -- probably not
  std::size_t hash() const override { return (std::size_t) boolector_get_node_id(btor, node); };
  bool compare(const std::unique_ptr<TermAbs>& absterm) const override
  {
    BoolectorTerm* other = static_cast<BoolectorTerm*>(absterm.get());
    return boolector_get_node_id(this->btor, this->node) == boolector_get_node_id(other->btor, other->node);
  }
  std::vector<shared_ptr<BoolectorTerm>> get_children() const override
  {
    return children;
  }
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
  std::vector<shared_ptr<BoolectorTerm>> children;
  Op op;
};

}

#endif
