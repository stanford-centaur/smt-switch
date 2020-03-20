#pragma once

#include "solver.h"
#include "term_hashtable.h"

namespace smt {

class LoggingSolver : public AbsSmtSolver
{
 public:
  LoggingSolver(SmtSolver s);
  ~LoggingSolver();

  // implemented
  Sort make_sort(const SortKind sk) const override;
  Sort make_sort(const SortKind sk, uint64_t size) const override;
  Sort make_sort(const SortKind sk, const Sort & sort1) const override;
  Sort make_sort(const SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2) const override;
  Sort make_sort(const SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2,
                 const Sort & sort3) const override;
  Sort make_sort(const SortKind sk, const SortVec & sorts) const override;
  Term make_term(bool b) const override;
  Term make_term(int64_t i, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  Term make_term(const Op op, const Term & t) const override;
  Term make_term(const Op op, const Term & t0, const Term & t1) const override;
  Term make_term(const Op op,
                 const Term & t0,
                 const Term & t1,
                 const Term & t2) const override;
  Term make_term(const Op op, const TermVec & terms) const override;
  // Will probably remove this eventually
  // For now, need to clear the hash table
  void reset() override;

  // dispatched to underlying solver
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) const override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  Term get_value(Term & t) const override;
  void reset_assertions() override;

 protected:
  TermHashTable hashtable;
};

}  // namespace smt
