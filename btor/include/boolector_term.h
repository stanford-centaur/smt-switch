#ifndef SMT_BOOLECTOR_TERM_H
#define SMT_BOOLECTOR_TERM_H

#include <vector>

#include "boolector.h"

#include "term.h"
#include "utils.h"

#include "boolector_sort.h"

namespace smt {

// forward declaration
class BoolectorSolver;

class BoolectorTermIter : public TermIterBase
{
 public:
  BoolectorTermIter(const std::vector<Term>::const_iterator v_it)
      : v_it(v_it){};
  BoolectorTermIter(const BoolectorTermIter & it) { v_it = it.v_it; };
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
  std::vector<Term>::const_iterator v_it;
};

class BoolectorTerm : public AbsTerm
{
 public:
  BoolectorTerm(
      Btor * b, BoolectorNode * n, std::vector<Term> c, Op o, bool is_sym)
      : btor(b), node(n), children(c), op(o), is_sym(is_sym)
  {
    // set the btor node symbol, for retrieving string representation later
    // Note: vars and constants already have ways of retrieving char
    // representation
    if (c.size())
    {
      std::string btor_node_repr("(");
      btor_node_repr += op.to_string();
      for (auto t : c)
      {
        btor_node_repr += " " + t->to_string();
      }
      btor_node_repr += ")";
      boolector_set_symbol(btor, n, btor_node_repr.c_str());
    }
  };
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
  std::vector<Term> children;
  Op op;
  bool is_sym;

  friend class BoolectorSolver;
  friend class BoolectorTermIter;
};

}  // namespace smt

#endif
