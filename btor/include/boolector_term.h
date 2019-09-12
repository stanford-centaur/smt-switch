#ifndef SMT_BOOLECTOR_TERM_H
#define SMT_BOOLECTOR_TERM_H

#include <vector>

#include "boolector.h"
#include "btornode.h"
#include "utils/btornodeiter.h"

#include "term.h"
#include "utils.h"

#include "boolector_sort.h"

namespace smt {

// forward declaration
class BoolectorSolver;

// helpers
Op lookup_op(Btor * btor, BoolectorNode * n, std::vector<BtorNode *> & children);

class BoolectorTermIter : public TermIterBase
{
 public:
  BoolectorTermIter(Btor * btor, std::vector<BtorNode *>::const_iterator v_it)
    : btor(btor), v_it(v_it) {};
  BoolectorTermIter(const BoolectorTermIter & it) { btor = it.btor; v_it = it.v_it; };
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
  std::vector<BtorNode *>::const_iterator v_it;
};

class BoolectorTerm : public AbsTerm
{
 public:
  BoolectorTerm(
      Btor * b, BoolectorNode * n);
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
  BoolectorNode * node;
  BtorNode * bn;
  std::vector<BtorNode *> children;
  Op op;
  bool is_sym;

  friend class BoolectorSolver;
  friend class BoolectorTermIter;
};

}  // namespace smt

#endif
