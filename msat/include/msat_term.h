/*********************                                                        */
/*! \file msat_term.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief MathSAT implementation of AbsTerm
**
**
**/

#ifndef SMT_MSAT_TERM_H
#define SMT_MSAT_TERM_H

#include "term.h"
#include "utils.h"

#include "mathsat.h"

namespace smt {

// forward declaration
class MsatSolver;
class MsatInterpolatingSolver;

class MsatTermIter : public TermIterBase
{
 public:
  // TODO: consider making env const everywhere
  MsatTermIter(msat_env e, const msat_term t, uint32_t p)
      : env(e), term(t), pos(p){};
  MsatTermIter(const MsatTermIter & it);
  ~MsatTermIter(){};
  MsatTermIter & operator=(const MsatTermIter & it);
  void operator++() override;
  const Term operator*() override;
  TermIterBase * clone() const override;
  bool operator==(const MsatTermIter & it);
  bool operator!=(const MsatTermIter & it);

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  msat_env env;
  msat_term term;
  uint32_t pos;
};

class MsatTerm : public AbsTerm
{
 public:
  MsatTerm(msat_env e, msat_term t) : env(e), term(t), is_uf(false)
  {
    // should know that decl is invalid
    (decl).repr = NULL;
  };
  MsatTerm(msat_env e, msat_decl d) : env(e), decl(d), is_uf(true)
  {
    // should know that term is invalid
    MSAT_MAKE_ERROR_TERM(term);
  };
  ~MsatTerm(){};
  std::size_t hash() const override;
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

 protected:
  msat_env env;
  msat_term term;
  msat_decl decl;
  bool is_uf;  ///< set to true if wrapping a msat_decl (e.g. an uninterpreted
               ///< function)

  friend class MsatSolver;
  friend class MsatInterpolatingSolver;
};

}  // namespace smt

#endif
