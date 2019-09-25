#ifndef SMT_BOOLECTOR_SOLVER_H
#define SMT_BOOLECTOR_SOLVER_H

#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include "boolector_extensions.h"
#include "boolector_sort.h"
#include "boolector_term.h"

#include "exceptions.h"
#include "result.h"
#include "smt.h"
#include "sort.h"

namespace smt {
/**
   Boolector Solver
 */
class BoolectorSolver : public AbsSmtSolver
{
 public:
  // might have to use std::unique_ptr<Btor>(boolector_new) and move it?
  BoolectorSolver() : btor(boolector_new())
  {
    // set termination function -- throw an exception
    auto throw_exception = [](const char * msg) -> void {
      throw InternalSolverException(msg);
    };
    boolector_set_abort(throw_exception);
  };
  BoolectorSolver(const BoolectorSolver &) = delete;
  BoolectorSolver & operator=(const BoolectorSolver &) = delete;
  ~BoolectorSolver() { boolector_delete(btor); };
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
  Sort make_sort(SortKind sk,
                 const Sort & idxsort,
                 const Sort & elemsort) const override;
  Sort make_sort(SortKind sk,
                 const std::vector<Sort> & sorts,
                 const Sort & sort) const override;
  Term make_value(bool b) const override;
  Term make_value(unsigned int i, const Sort & sort) const override;
  Term make_value(const std::string val,
                  const Sort & sort,
                  unsigned int base = 10) const override;
  Term make_value(const Term & val, const Sort & sort) const override;
  Term make_term(const std::string s, const Sort & sort) override;
  /* build a new term */
  Term make_term(Op op, const Term & t) const override;
  Term make_term(Op op, const Term & t0, const Term & t1) const override;
  Term make_term(Op op,
                 const Term & t0,
                 const Term & t1,
                 const Term & t2) const override;
  Term make_term(Op op, const std::vector<Term> & terms) const override;
  void reset() override;
  void reset_assertions() override;
  bool has_symbol(const std::string name) const override;
  Term lookup_symbol(const std::string name) const override;
  virtual Term substitute(
      const Term term,
      const UnorderedTermMap & substitution_map) const override;
  // helper methods for making a term with a primitive op
  Term apply_prim_op(PrimOp op, Term t) const;
  Term apply_prim_op(PrimOp op, Term t0, Term t1) const;
  Term apply_prim_op(PrimOp op, Term t0, Term t1, Term t2) const;
  Term apply_prim_op(PrimOp op, std::vector<Term> terms) const;
  void dump_smt2(FILE * file) const override;

 protected:
  Btor * btor;
  // store the names of created symbols for has_symbol
  std::unordered_set<std::string> symbol_names;
};
}  // namespace smt

#endif
