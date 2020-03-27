#ifndef SMT_YICES2_TERM_H
#define SMT_YICES2_TERM_H

#include <vector>

#include "gmp.h"
#include "term.h"
#include "utils.h"
#include "yices.h"

#include "yices2_sort.h"

namespace smt {

// forward declaration
class Yices2Solver;

class Yices2TermIter : public TermIterBase
{
 public:
  Yices2TermIter(term_t t, uint32_t p) : term(t), pos(p){};
  Yices2TermIter(const Yices2TermIter & it);
  ~Yices2TermIter(){};
  Yices2TermIter & operator=(const Yices2TermIter & it);
  void operator++() override;
  const Term operator*() override;
  TermIterBase * clone() const override;
  bool operator==(const Yices2TermIter & it);
  bool operator!=(const Yices2TermIter & it);

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  term_t term;
  uint32_t pos;
};

class Yices2Term : public AbsTerm
{
 public:
  Yices2Term(term_t t) : term(t){};
  Yices2Term(term_t t, bool is_fun) : term(t), is_function(is_fun){};
  ~Yices2Term(){};
  std::size_t hash() const override;
  bool compare(const Term & absterm) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  bool is_symbolic_const() const override;
  bool is_value() const override;
  virtual std::string to_string() const override;
  uint64_t to_int() const override;
  /* Iterators for traversing the children */
  TermIter begin() override;
  TermIter end() override;

 protected:
  term_t term;
  bool is_function;

  friend class Yices2Solver;
  friend class Yices2TermIter;
};

}  // namespace smt

#endif
