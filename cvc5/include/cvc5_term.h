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

#pragma once

#include "term.h"
#include "utils.h"

#include "api/cpp/cvc5.h"

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
  class Cvc5Solver;

  class Cvc5TermIter : public TermIterBase
  {
  public:
   Cvc5TermIter(::CVC4::api::Term term, uint32_t p = 0) : term(term), pos(p){};
   Cvc5TermIter(const Cvc5TermIter & it) { term = it.term; pos = it.pos; };
   ~Cvc5TermIter(){};
   Cvc5TermIter & operator=(const Cvc5TermIter & it);
   void operator++() override;
   const Term operator*() override;
   TermIterBase * clone() const override;
   bool operator==(const Cvc5TermIter & it);
   bool operator!=(const Cvc5TermIter & it);

  protected:
    bool equal(const TermIterBase & other) const override;

  private:
   ::CVC4::api::Term term;
   uint32_t pos;
  };

  class Cvc5Term : public AbsTerm
  {
  public:
    Cvc5Term(CVC4::api::Term t) : term(t) {};
    ~Cvc5Term() {};
    std::size_t hash() const override;
    std::size_t get_id() const override;
    bool compare(const Term & absterm) const override;
    Op get_op() const override;
    Sort get_sort() const override;
    bool is_symbol() const override;
    bool is_param() const override;
    bool is_symbolic_const() const override;
    bool is_value() const override;
    virtual std::string to_string() override;
    uint64_t to_int() const override;
    /** Iterators for traversing the children
     */
    TermIter begin() override;
    TermIter end() override;
    std::string print_value_as(SortKind sk) override;

    // getters for solver-specific objects
    // for interacting with third-party CVC4-specific software
    ::CVC4::api::Term get_cvc4_term() const { return term; };

   protected:
    CVC4::api::Term term;

  friend class Cvc5Solver;
  friend class CVC4InterpolatingSolver;
  };



}
