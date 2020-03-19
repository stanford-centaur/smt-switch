#pragma once

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
  TermIter begin();
  TermIter end();

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
};

}  // namespace smt
