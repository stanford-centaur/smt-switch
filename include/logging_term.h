#pragma once

#include "ops.h"
#include "smt_defs.h"
#include "term.h"

namespace smt {

class LoggingTerm : public AbsTerm
{
 public:
  LoggingTerm(Term t, Sort s, Op o, TermVec c);
  virtual ~LoggingTerm();

  // implemented
  bool compare(const Term & t) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  std::string to_string() const override;
  TermIter begin() override;
  TermIter end() override;

  // dispatched to underlying term
  std::size_t hash() const override;
  bool is_symbolic_const() const override;
  bool is_value() const override;
  uint64_t to_int() const override;

 protected:
  Term term;
  Sort sort;
  Op op;
  TermVec children;

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
