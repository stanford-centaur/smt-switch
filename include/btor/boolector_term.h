#ifndef SMT_BOOLECTOR_TERM_H
#define SMT_BOOLECTOR_TERM_H

#include <vector>

#include "boolector/boolector.h"

#include "fun.h"
#include "term.h"
#include "utils.h"

#include "boolector_fun.h"
#include "boolector_sort.h"

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
  BoolectorTermIter& operator=(const BoolectorTermIter& it);
    void operator++() override;
    void operator++(int junk);
    const Term operator*() const override;
    bool operator==(const BoolectorTermIter& it);
    bool operator!=(const BoolectorTermIter& it);

 protected:
    bool equal(const TermIterBase& other) const override;

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
  ~BoolectorTerm();
  // TODO: check if this is okay -- probably not
  std::size_t hash() const override;
    bool compare(const Term& absterm) const override;
    std::vector<Term> get_children() const override;
    Fun get_fun() const override;
    Sort get_sort() const override;
    virtual std::string to_string() const override;
    std::string as_bitstr() const override;
  /** Iterators for traversing the children
   */
    TermIter begin() override;
    TermIter end() override;

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
