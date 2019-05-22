#ifndef SMT_SOLVER_H
#define SMT_SOLVER_H

#include <memory>
#include <string>
#include <vector>

#include "exceptions.h"
#include "func.h"
#include "sort.h"
#include "term.h"

namespace smt
{
  /**
     Abstract solver class to be implemented by each supported solver.
   */
  class AbsSmtSolver
  {
  public:
    AbsSmtSolver() {};
    virtual ~AbsSmtSolver() {};
    virtual void set_opt(const std::string option, bool value) const = 0;
    virtual void set_opt(const std::string option,
                         const std::string value) const = 0;
    virtual Sort declare_sort(const std::string name, unsigned int arity) const = 0;
    virtual Term declare_const(const std::string name, Sort sort) const = 0;
    // virtual UF declare_fun(const std::string name,
    //                              const std::vector<Sort>& sorts,
    //                              Sort sort) const = 0;
    virtual Term make_const(unsigned int i, Sort sort) const = 0;
    virtual void assert_formula(const Term &t) const = 0;
    virtual bool check_sat() const = 0;
    virtual Term get_value(Term &t) const = 0;
    // virtual bool check_sat_assuming() const = 0;
    virtual Sort make_sort(Kind k) const = 0;
    virtual Sort make_sort(Kind k, unsigned int size) const = 0;
    virtual Sort make_sort(Kind k, Sort idxsort, Sort elemsort) const = 0;
    virtual Sort make_sort(Kind k, std::vector<Sort> sorts,
                                Sort sort) const = 0;
    virtual Func make_op(PrimOp op, unsigned int idx) const = 0;
    virtual Func make_op(PrimOp op, unsigned int idx0,
                              unsigned int idx1) const = 0;
    virtual Term apply_func(PrimOp op, Term t) const = 0;
    virtual Term apply_func(PrimOp op, Term t0, Term t1) const = 0;
    virtual Term apply_func(PrimOp op, Term t0, Term t1, Term t2) const = 0;
    virtual Term apply_func(PrimOp op, std::vector<Term> terms) const = 0;
    virtual Term apply_func(Func fun, Term t) const = 0;
    virtual Term apply_func(Func fun, Term t0, Term t1) const = 0;
    virtual Term apply_func(Func fun, Term t0, Term t1, Term t2) const = 0;
    virtual Term apply_func(Func fun, std::vector<Term> terms) const = 0;
    /* convenience methods */
    Term extract(unsigned int u, unsigned int l, Term t)
    {
      return apply_func(make_op(EXTRACT, u, l), t);
    }
    Term zero_extend(unsigned int i, Term t)
    {
      return apply_func(make_op(ZERO_EXTEND, i), t);
    }
    Term sign_extend(unsigned int i, Term t)
    {
      return apply_func(make_op(SIGN_EXTEND, i), t);
    }
  };

  using SmtSolver = std::shared_ptr<AbsSmtSolver>;
}

#endif
