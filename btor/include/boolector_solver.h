#ifndef SMT_BOOLECTOR_SOLVER_H
#define SMT_BOOLECTOR_SOLVER_H

#include <memory>
#include <string>
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
    // to support resetting assertions, wrap everything in a push/pop
    // TODO: replace this with a proper implementation
    boolector_set_opt(btor, BTOR_OPT_INCREMENTAL, 1);
    boolector_push(btor, 1);
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
  Sort make_sort(SortKind sk, Sort idxsort, Sort elemsort) const override;
  Sort make_sort(SortKind sk,
                 std::vector<Sort> sorts,
                 Sort sort) const override;
  Term make_value(bool b) const override;
  Term make_value(unsigned int i, Sort sort) const override;
  Term make_value(const std::string val, Sort sort) const override;
  Term make_term(const std::string s, Sort sort) override;
  /* build a new term */
  Term make_term(Op op, Term t) const override;
  Term make_term(Op op, Term t0, Term t1) const override;
  Term make_term(Op op, Term t0, Term t1, Term t2) const override;
  Term make_term(Op op, std::vector<Term> terms) const override;
  void reset() override;
  void reset_assertions() override;
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
