#ifndef SMT_CVC4_TERM_H
#define SMT_CVC4_TERM_H

#include "fun.h"
#include "term.h"
#include "utils.h"

#include "api/cvc4cpp.h"

namespace smt {
  //forward declaration
  class CVC4Solver;

  // TODO: Implement this
  /* class CVC4TermIter : public TermIterBase */
  /* { */

  /* }; */

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
