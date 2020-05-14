#pragma once

#include "ops.h"
#include "smt_defs.h"
#include "term.h"

namespace smt {

class LoggingTerm : public AbsTerm
{
 public:
  LoggingTerm(Term t, Sort s, Op o, TermVec c);
  // this one is for making symbols
  // passing a name implies it's a symbol
  LoggingTerm(Term t, Sort s, Op o, TermVec c, std::string r);
  virtual ~LoggingTerm();

  // implemented

  /** Returns true iff the underlying term AND sort are equivalent
   *  @param t the term to compare with (assumed to be LoggingTerm)
   *  @return true iff the underlying term and sort match t
   */
  bool compare(const Term & t) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  std::string to_string() override;
  bool is_symbolic_const() const override;
  TermIter begin() override;
  TermIter end() override;

  // dispatched to underlying term
  std::size_t hash() const override;
  bool is_value() const override;
  uint64_t to_int() const override;

 protected:
  Term wrapped_term;  ///< the term of the underlying solver
  Sort sort;          ///< a LoggingSort
  Op op;
  TermVec children;
  std::string repr;
  bool is_symbol;

  // So LoggingSolver can access protected members:
  friend class LoggingSolver;
};

class LoggingTermIter : public TermIterBase
{
 public:
  LoggingTermIter(TermVec::iterator i);
  LoggingTermIter(const LoggingTermIter & lit);
  ~LoggingTermIter();
  LoggingTermIter & operator=(const LoggingTermIter & lit);
  void operator++() override;
  const Term operator*() override;
  TermIterBase * clone() const override;
  bool operator==(const LoggingTermIter & lit);
  bool operator!=(const LoggingTermIter & lit);

 protected:
  bool equal(const TermIterBase & other) const override;
  TermVec::iterator it;
};

}  // namespace smt
