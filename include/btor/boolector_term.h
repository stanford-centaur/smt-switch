#ifndef SMT_BOOLECTOR_TERM_H
#define SMT_BOOLECTOR_TERM_H

#include <vector>

#include "boolector/boolector.h"
#include "term.h"
#include "op.h"

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
  Sort get_sort() const override {
    Sort sort;
    BoolectorSort s = boolector_get_sort(btor, node);
    if (boolector_is_bitvec_sort(btor, s)) {
      unsigned int width = boolector_get_width(btor, node);
      // increment reference counter for the sort
      boolector_copy_sort(btor, s);
      sort = std::make_shared<BoolectorBVSort>(btor, s, width);
    } else if (boolector_is_array_sort(btor, s)) {
      unsigned int idxwidth = boolector_get_index_width(btor, node);
      unsigned int elemwidth = boolector_get_width(btor, node);
      // Note: Boolector does not support multidimensional arrays
      std::shared_ptr<BoolectorSortBase> idxsort =
          std::make_shared<BoolectorBVSort>(
              btor, boolector_bitvec_sort(btor, idxwidth), idxwidth);
      std::shared_ptr<BoolectorSortBase> elemsort =
          std::make_shared<BoolectorBVSort>(
              btor, boolector_bitvec_sort(btor, elemwidth), elemwidth);
      // increment reference counter for the sort
      boolector_copy_sort(btor, s);
      sort = std::make_shared<BoolectorArraySort>(btor, s, idxsort, elemsort);
    } else {
      // Note: functions are not terms, and thus we don't need to check for
      // fun_sort unreachable
      assert(false);
    }
    return sort;
  }
  virtual std::string to_string() const override
  {
    throw NotImplementedException("Can't get string representation from btor");
  }
  std::string as_bitstr() const override {
    if (!std::holds_alternative<PrimOp>(op) ||
        (std::get<PrimOp>(op) != CONST)) {
      throw IncorrectUsageException(
          "Can't get bitstring from a non-constant term.");
    }
    return std::string(boolector_bv_assignment(btor, node));
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
