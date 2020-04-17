#ifndef SMT_YICES2_SOLVER_H
#define SMT_YICES2_SOLVER_H

#include <gmp.h>
#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include <yices.h>

#include "yices2_extensions.h"
#include "yices2_sort.h"
#include "yices2_term.h"

#include "exceptions.h"
#include "result.h"
#include "smt.h"
#include "sort.h"

namespace smt {
/**
   Yices2 Solver
 */
class Yices2Solver : public AbsSmtSolver
{
 public:
  Yices2Solver()
  {
    // Had to move yices_init to the Factory
    // yices_init();
    ctx = yices_new_context(NULL);
    config = yices_new_config();
  };
  Yices2Solver(const Yices2Solver &) = delete;
  Yices2Solver & operator=(const Yices2Solver &) = delete;
  ~Yices2Solver()
  {
    yices_free_config(config);
    yices_free_context(ctx);

    // TODO: Should probably find a good place to
    // call yices_exit.
    // yices_exit();
  };
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  Term get_value(Term & t) const override;
  Sort make_sort(const std::string name, uint64_t arity) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, uint64_t size) const override;
  Sort make_sort(SortKind sk, const Sort & sort1) const override;
  Sort make_sort(SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2) const override;
  Sort make_sort(SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2,
                 const Sort & sort3) const override;
  Sort make_sort(SortKind sk, const SortVec & sorts) const override;
  Term make_term(bool b) const override;
  Term make_term(int64_t i, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  /* build a new term */
  Term make_term(Op op, const Term & t) const override;
  Term make_term(Op op, const Term & t0, const Term & t1) const override;
  Term make_term(Op op,
                 const Term & t0,
                 const Term & t1,
                 const Term & t2) const override;
  Term make_term(Op op, const TermVec & terms) const override;
  void reset() override;
  void reset_assertions() override;
  Term substitute(const Term term,
                  const UnorderedTermMap & substitution_map) const override;
  void dump_smt2(FILE * file) const override;

 protected:
  mutable context_t * ctx;
  mutable ctx_config_t * config;
};
}  // namespace smt

#endif