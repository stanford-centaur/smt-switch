#ifndef SMT_CVC4_SOLVER_H
#define SMT_CVC4_SOLVER_H

#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "cvc4_sort.h"
#include "cvc4_term.h"

#include "api/cvc4cpp.h"

#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "smt.h"
#include "sort.h"
#include "term.h"

namespace smt {
/**
   CVC4 Solver
 */
class CVC4Solver : public AbsSmtSolver
{
 public:
  CVC4Solver() : solver(::CVC4::api::Solver())
  {
    solver.setOption("lang", "smt2");
  };
  CVC4Solver(const CVC4Solver &) = delete;
  CVC4Solver & operator=(const CVC4Solver &) = delete;
  ~CVC4Solver() { };
  void set_opt(const std::string option, bool value) const override;
  void set_opt(const std::string option,
               const std::string value) const override;
  void set_logic(const std::string logic) const override;
  void assert_formula(const Term & t) const override;
  Result check_sat() const override;
  Result check_sat_assuming(const TermVec & assumptions) const override;
  void push(unsigned int num = 1) const override;
  void pop(unsigned int num = 1) const override;
  Term get_value(Term & t) const override;
  Sort make_sort(const std::string name, unsigned int arity) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, unsigned int size) const override;
  Sort make_sort(SortKind sk, Sort idxsort, Sort elemsort) const override;
  Sort make_sort(SortKind sk,
                 std::vector<Sort> sorts,
                 Sort sort) const override;
  Term make_value(bool b) const override;
  Term make_value(unsigned int i, Sort sort) const override;
  Term make_value(const std::string val, Sort sort, unsigned int base = 10) const override;
  Term make_value(const Op op, const Term val, const Sort sort) const override;
  Term make_term(const std::string s, Sort sort) override;
  /* build a new term */
  Term make_term(Op op, Term t) const override;
  Term make_term(Op op, Term t0, Term t1) const override;
  Term make_term(Op op, Term t0, Term t1, Term t2) const override;
  Term make_term(Op op, std::vector<Term> terms) const override;
  void reset() override;
  void reset_assertions() override;
  bool has_symbol(const std::string name) const override;
  Term lookup_symbol(const std::string name) const override;
  void dump_smt2(FILE * file) const override;
  // helpers
  ::CVC4::api::OpTerm make_op_term(Op op) const;

 protected:
  ::CVC4::api::Solver solver;
  // keep track of created symbols for has_symbol and lookup_symbol
  std::unordered_map<std::string, Term> symbols;
};
}  // namespace smt

#endif
