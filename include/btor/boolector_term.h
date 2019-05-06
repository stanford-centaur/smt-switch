#ifndef SMT_BOOLECTOR_TERM_H
#define SMT_BOOLECTOR_TERM_H

#include <iostream>
#include <vector>

#include "boolector/boolector.h"
#include "term.h"
#include "op.h"

// TODO: Figure out if we should have extern C here?
//       seems to be working already

namespace smt {

// forward declaration
class BoolectorSolver;

class BoolectorTerm : public AbsTerm
{
 public:
   BoolectorTerm(Btor *b, BoolectorNode *n, std::vector<Term> c, Op o)
       : btor(b), node(n), children(c), op(o){};
   ~BoolectorTerm() { boolector_release(btor, node); }
   // TODO: check if this is okay -- probably not
   std::size_t hash() const override {
     return (std::size_t)boolector_get_node_id(btor, node); };
   bool compare(const Term & absterm) const override {
     std::shared_ptr<BoolectorTerm> other = std::static_pointer_cast<BoolectorTerm>(absterm);
     return boolector_get_node_id(this->btor, this->node) ==
            boolector_get_node_id(other->btor, other->node);
  }
  std::vector<Term> get_children() const override { return children; }
  Op get_op() const override { return op; };
  // TODO Probably would be best to store this information at the API level
  //      want solvers to be identical to the user (except for supported logics
  //      of course)
  Sort get_sort() const override {
    // TODO: might need to support this -- need to know the sort to even get the value
    //       decide between either reconstructing it using boolector functions
    //       or storing it explicitly (this would require knowing which sort an operation results in...)
    throw NotImplementedException("Can't get sort from btor");
  }
  virtual std::string to_string() const override
  {
    throw NotImplementedException("Can't get string representation from btor");
  }
 protected:
  Btor * btor;
  BoolectorNode * node;
  std::vector<Term> children;
  Op op;

  friend class BoolectorSolver;
};

}

#endif
