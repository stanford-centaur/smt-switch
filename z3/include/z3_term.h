#ifndef SMT_Z3_TERM_H
#define SMT_Z3_TERM_H

#include "term.h"
#include "utils.h"

#include "z3++.h"

namespace smt {
  //forward declaration
  class Z3Solver;

  class Z3TermIter : public TermIterBase
  {
  public:
    Z3TermIter(const ::z3::ast_vector_tpl::iterator term_it)
      : term_it(term_it){};
    Z3TermIter(const CVC4TermIter & it) { term_it = it.term_it; };
    ~Z3TermIter() {};
    Z3TermIter & operator=(const CVC4TermIter & it);
    void operator++() override;
    void operator++(int junk);
    const Term operator*() override;
    bool operator==(const CVC4TermIter & it);
    bool operator!=(const CVC4TermIter & it);

  protected:
    bool equal(const TermIterBase & other) const override;

  private:
    ::z3::ast_vector_tpl::iterator term_it;
  };

  class Z3Term : public AbsTerm
  {
  public:
    Z3Term(::z3::ast term t) : term(t) {};
    ~Z3Term() {};
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
    ::z3::ast term;

  friend class Z3Solver;
  };

}

#endif
