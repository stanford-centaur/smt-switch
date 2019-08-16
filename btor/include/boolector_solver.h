#ifndef SMT_BOOLECTOR_SOLVER_H
#define SMT_BOOLECTOR_SOLVER_H

#include <memory>
#include <string>
#include <vector>

#include "boolector_extensions.h"
#include "boolector_fun.h"
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
  BoolectorSolver() : btor(boolector_new()){};
  BoolectorSolver(const BoolectorSolver &) = delete;
  BoolectorSolver & operator=(const BoolectorSolver &) = delete;
  ~BoolectorSolver() { boolector_delete(btor); };
  void set_opt(const std::string option, bool value) const override;
  void set_opt(const std::string option,
               const std::string value) const override;
  void set_logic(const std::string logic) const override;
  void assert_formula(const Term & t) const override;
  Result check_sat() const override;
  Term get_value(Term & t) const override;
  Sort make_sort(const std::string name,
                         unsigned int arity) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, unsigned int size) const override;
  Sort make_sort(SortKind sk, Sort idxsort, Sort elemsort) const override;
  Sort make_sort(SortKind sk, std::vector<Sort> sorts, Sort sort) const override;
  Term make_value(bool b) const override;
  Term make_value(unsigned int i, Sort sort) const override;
  Term make_value(const std::string val, Sort sort) const override;
  Term make_term(const std::string s, Sort sort) const override;
  /* build a new term */
  Term make_term(Op op, Term t) const override;
  Term make_term(Op op, Term t0, Term t1) const override;
  Term make_term(Op op, Term t0, Term t1, Term t2) const override;
  Term make_term(Op op, std::vector<Term> terms) const override;
  // helper methods for making a term with a primitive op
  Term apply_prim_op(PrimOp op, Term t) const;
  Term apply_prim_op(PrimOp op, Term t0, Term t1) const;
  Term apply_prim_op(PrimOp op, Term t0, Term t1, Term t2) const;
  Term apply_prim_op(PrimOp op, std::vector<Term> terms) const;
 protected:
  Btor * btor;
};
}  // namespace smt

#endif
