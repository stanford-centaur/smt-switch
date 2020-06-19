/*********************                                                        */
/*! \file cvc4_term.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief CVC4 implementation of AbsTerm
**
**
**/

#ifndef SMT_CVC4_TERM_H
#define SMT_CVC4_TERM_H

#include "term.h"
#include "utils.h"

#include "api/cvc4cpp.h"

// define hash for old compilers
namespace std
{

// specialize hash struct
template<>
struct hash<::CVC4::api::Kind>
{
  size_t operator()(const ::CVC4::api::Kind k) const
  {
    return static_cast<std::size_t>(k);
  }
};

}

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
    const Term operator*() override;
    TermIterBase * clone() const override;
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
    Op get_op() const override;
    Sort get_sort() const override;
    bool is_symbolic_const() const override;
    bool is_value() const override;
    virtual std::string to_string() override;
    uint64_t to_int() const override;
    /** Iterators for traversing the children
     */
    TermIter begin() override;
    TermIter end() override;
    std::string print_value_as(SortKind sk) override;

   protected:
    CVC4::api::Term term;

  friend class CVC4Solver;
  friend class CVC4InterpolatingSolver;
  };



}

#endif
