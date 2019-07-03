#ifndef SMT_CVC4_TERM_H
#define SMT_CVC4_TERM_H

#include "fun.h"
#include "term.h"
#include "utils.h"

#include "api/cvc4cpp.h"

namespace smt {
  //forward declaration
  class CVC4Solver;

  class CVC4TermIter : public TermIterBase
  {
  public:
    CVC4TermIter(const ::CVC4::api::Term::const_iterator term_it)
      : term_it(term_it){};
    CVC4TermIter(const CVC4TermIter & it) { term_it = it.term_it; };
    ~CVC4TermIter() {};
    CVC4TermIter & operator=(const CVC4TermIter & it);
    void operator++() override;
    void operator++(int junk);
    const Term operator*() const override;
    bool operator==(const CVC4TermIter & it);
    bool operator!=(const CVC4TermIter & it);

  protected:
    bool equal(const TermIterBase & other) const override;

  private:
    ::CVC4::api::Term::const_iterator term_it;
  };

  class CVC4Term : public AbsTerm
  {
  public:
    CVC4Term(CVC4::api::Term t) : term(t) {};
    ~CVC4Term() {};
    std::size_t hash() const override;
    bool compare(const Term & absterm) const override;
    Fun get_fun() const override;
    Sort get_sort() const override;
    virtual std::string to_string() const override;
    uint64_t to_int() const override;
    /** Iterators for traversing the children
     */
    TermIter begin() override;
    TermIter end() override;

  protected:
    CVC4::api::Term term;

  friend class CVC4Solver;
  };

}

#endif
