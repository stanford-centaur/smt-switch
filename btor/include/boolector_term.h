#ifndef SMT_BOOLECTOR_TERM_H
#define SMT_BOOLECTOR_TERM_H

#include <vector>

#include "boolector.h"
extern "C" {
#include "btorcore.h"
#include "btornode.h"
#include "utils/btornodeiter.h"
}

#include "term.h"
#include "utils.h"

#include "boolector_sort.h"

namespace smt {

// forward declaration
class BoolectorSolver;

// helpers
Op lookup_op(Btor * btor, BoolectorNode * n);

class BoolectorTermIter : public TermIterBase
{
 public:
  // IMPORTANT: The correctness of this code depends on the array e being of size 3
  BoolectorTermIter(Btor * btor, BtorNode* (& refarray)[3], int total_idx, int arity)
    : btor(btor), total_idx(total_idx), arity(arity), idx_access(0)
  {
    for (size_t i = 0; i < arity; i++)
    {
      e[i] = refarray[i];
    }
  }
  BoolectorTermIter(const BoolectorTermIter & it)
  {
    btor = it.btor;
    total_idx = it.total_idx;
    arity = it.arity;
    idx_access = it.idx_access;
    for (size_t i = 0; i < arity; i++)
    {
      e[i] = it.e[i];
    }
  };
  ~BoolectorTermIter(){};
  BoolectorTermIter & operator=(const BoolectorTermIter & it);
  void operator++() override;
  void operator++(int junk);
  const Term operator*() const override;
  bool operator==(const BoolectorTermIter & it);
  bool operator!=(const BoolectorTermIter & it);

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  Btor * btor;
  BtorNode* e[3];
  int total_idx;
  int arity;
  int idx_access;
};

class BoolectorTerm : public AbsTerm
{
 public:
  BoolectorTerm(Btor * b, BoolectorNode * n);
  ~BoolectorTerm();
  std::size_t hash() const override;
  bool compare(const Term & absterm) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  bool is_symbolic_const() const override;
  bool is_value() const override;
  virtual std::string to_string() const override;
  uint64_t to_int() const override;
  /** Iterators for traversing the children
   */
  TermIter begin() override;
  TermIter end() override;

 protected:
  Btor * btor;
  // the actual API level node that is used
  BoolectorNode * node;
  // the real address of the boolector node
  // allows us to look up:
  //   kind: for retrieving operator
  //   e:    for getting children
  BtorNode * bn;
  // true iff the node is negated
  bool negated;
  // true iff the node is a symbolic constant
  bool is_sym;

  friend class BoolectorSolver;
  friend class BoolectorTermIter;
};

}  // namespace smt

#endif
