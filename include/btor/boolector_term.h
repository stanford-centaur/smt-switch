#ifndef SMT_BOOLECTOR_TERM_H
#define SMT_BOOLECTOR_TERM_H

#include <vector>

#include "boolector/boolector.h"
#include "fun.h"
#include "term.h"
#include "utils.h"

namespace smt {

// forward declaration
class BoolectorSolver;

class BoolectorTermIter : public TermIterBase
{
 public:
  BoolectorTermIter(const std::vector<Term>::const_iterator v_it)
      : v_it(v_it){};
  BoolectorTermIter(const BoolectorTermIter& it) { v_it = it.v_it; };
  ~BoolectorTermIter(){};
  // TODO: Check if this is necessary
  BoolectorTermIter& operator=(const BoolectorTermIter& it)
  {
    v_it = it.v_it;
    return *this;
  };
  void operator++() override
  {
    BoolectorTermIter self = *this;
    v_it++;
  };
  void operator++(int junk) { v_it++; };
  const Term operator*() const override { return *v_it; };
  bool operator==(const BoolectorTermIter& it) { return v_it == it.v_it; };
  bool operator!=(const BoolectorTermIter& it) { return v_it != it.v_it; };

 protected:
  bool equal(const TermIterBase& other) const override
  {
    // guaranteed to be safe by caller of equal (TermIterBase)
    const BoolectorTermIter& bti = static_cast<const BoolectorTermIter&>(other);
    return v_it == bti.v_it;
  }

 private:
  std::vector<Term>::const_iterator v_it;
};

class BoolectorTerm : public AbsTerm
{
 public:
  BoolectorTerm(Btor * b, BoolectorNode * n, std::vector<Term> c, Fun o)
      : btor(b), node(n), children(c), f(o){};
  BoolectorTerm(Btor * b, BoolectorNode * n, std::vector<Term> c, Op o)
      : btor(b), node(n), children(c), f(Fun(new BoolectorFun(o))){};
  BoolectorTerm(Btor * b, BoolectorNode * n, std::vector<Term> c, PrimOp o)
      : btor(b), node(n), children(c), f(Fun(new BoolectorFun(Op(o)))){};
  ~BoolectorTerm() { boolector_release(btor, node); }
  // TODO: check if this is okay -- probably not
  std::size_t hash() const override
  {
    return (std::size_t)boolector_get_node_id(btor, node);
  };
  bool compare(const Term& absterm) const override
  {
    std::shared_ptr<BoolectorTerm> other =
        std::static_pointer_cast<BoolectorTerm>(absterm);
    return boolector_get_node_id(this->btor, this->node)
           == boolector_get_node_id(other->btor, other->node);
  }
  std::vector<Term> get_children() const override { return children; }
  Fun get_fun() const override { return f; };
  Sort get_sort() const override {
    Sort sort;
    BoolectorSort s = boolector_get_sort(btor, node);
    if (boolector_is_bitvec_sort(btor, s))
    {
      unsigned int width = boolector_get_width(btor, node);
      // increment reference counter for the sort
      boolector_copy_sort(btor, s);
      sort = std::make_shared<BoolectorBVSort>(btor, s, width);
    }
    else if (boolector_is_array_sort(btor, s))
    {
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
    }
    else
    {
      Unreachable();
    }
    return sort;
  }
  virtual std::string to_string() const override
  {
    try
    {
      const char* btor_symbol = boolector_get_symbol(btor, node);
      std::string symbol(btor_symbol);
      return symbol;
    }
    catch (std::logic_error)
    {
      return "btor_expr";
    }
  }
  std::string as_bitstr() const override
  {
    if (!boolector_is_const(btor, node))
    {
      throw IncorrectUsageException(
          "Can't get bitstring from a non-constant term.");
    }
    const char* assignment = boolector_bv_assignment(btor, node);
    std::string s(assignment);
    boolector_free_bv_assignment(btor, assignment);
    return s;
  }

  /** Iterators for traversing the children
   */
  TermIter begin() override
  {
    return TermIter(new BoolectorTermIter(children.begin()));
  }

  TermIter end() override
  {
    return TermIter(new BoolectorTermIter(children.end()));
  }

 protected:
  Btor * btor;
  BoolectorNode * node;
  std::vector<Term> children;
  Fun f;

  friend class BoolectorSolver;
  friend class BoolectorTermIter;
};

}

#endif
