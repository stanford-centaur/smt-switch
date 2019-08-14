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
  Sort declare_sort(const std::string name, unsigned int arity) const override;
  Term declare_const(const std::string name, Sort sort) const override;
  // TODO implement declare_fun
  Fun declare_fun(const std::string name,
                  const std::vector<Sort> & sorts,
                  Sort sort) const override;
  Term make_value(bool b) const override;
  Term make_value(unsigned int i, Sort sort) const override;
  Term make_value(std::string val, Sort sort) const override;
  Fun make_fun(Op op) const override;
  void assert_formula(const Term & t) const override;
  Result check_sat() const override;
  Term get_value(Term & t) const override;
  Sort make_sort(SortCon sc) const override;
  Sort make_sort(SortCon sc, unsigned int size) const override;
  Sort make_sort(SortCon sc, Sort idxsort, Sort elemsort) const override;
  Sort make_sort(SortCon sc, std::vector<Sort> sorts, Sort sort) const override;
  // helper methods for applying a primitive op
  Term apply_prim_op(PrimOp op, Term t) const;
  Term apply_prim_op(PrimOp op, Term t0, Term t1) const;
  Term apply_prim_op(PrimOp op, Term t0, Term t1, Term t2) const;
  Term apply_prim_op(PrimOp op, std::vector<Term> terms) const;
  // Implementation of the AbsSmtSolver methods
  Term apply(Op op, Term t) const override;
  Term apply(Op op, Term t0, Term t1) const override;
  Term apply(Op op, Term t0, Term t1, Term t2) const override;
  Term apply(Op op, std::vector<Term> terms) const override;
  Term apply(Fun f, Term t) const override;
  Term apply(Fun f, Term t0, Term t1) const override;
  Term apply(Fun f, Term t0, Term t1, Term t2) const override;
  Term apply(Fun f, std::vector<Term> terms) const override;

 protected:
  Btor * btor;
};
}  // namespace smt

#endif
