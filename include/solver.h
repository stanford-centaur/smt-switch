#ifndef SMT_SOLVER_H
#define SMT_SOLVER_H

#include <string>
#include <vector>

#include "result.h"
#include "smt_defs.h"
#include "sort.h"

namespace smt {

/**
   Abstract solver class to be implemented by each supported solver.
 */
class AbsSmtSolver
{
 public:
  AbsSmtSolver(){};
  virtual ~AbsSmtSolver(){};
  virtual void set_opt(const std::string option, bool value) const = 0;
  virtual void set_opt(const std::string option,
                       const std::string value) const = 0;
  virtual void set_logic(const std::string logic) const = 0;
  virtual Sort declare_sort(const std::string name,
                            unsigned int arity) const = 0;
  virtual Term declare_const(const std::string name, Sort sort) const = 0;
  virtual Fun declare_fun(const std::string name,
                          const std::vector<Sort>& sorts,
                          Sort sort) const = 0;
  virtual Term make_value(bool b) const = 0;
  virtual Term make_value(unsigned int i, Sort sort) const = 0;
  virtual Term make_value(std::string val, Sort sort) const = 0;
  virtual Fun make_fun(Op op) const = 0;
  virtual void assert_formula(const Term& t) const = 0;
  virtual Result check_sat() const = 0;
  virtual Term get_value(Term& t) const = 0;
  // virtual bool check_sat_assuming() const = 0;
  virtual Sort make_sort(SortKind sk) const = 0;
  virtual Sort make_sort(SortKind sk, unsigned int size) const = 0;
  virtual Sort make_sort(SortKind sk, Sort idxsort, Sort elemsort) const = 0;
  virtual Sort make_sort(SortKind sk, std::vector<Sort> sorts, Sort sort) const = 0;
  virtual Term apply(Op op, Term t) const = 0;
  virtual Term apply(Op op, Term t0, Term t1) const = 0;
  virtual Term apply(Op op, Term t0, Term t1, Term t2) const = 0;
  virtual Term apply(Op op, std::vector<Term> terms) const = 0;
  virtual Term apply(Fun fun, Term t) const = 0;
  virtual Term apply(Fun fun, Term t0, Term t1) const = 0;
  virtual Term apply(Fun fun, Term t0, Term t1, Term t2) const = 0;
  virtual Term apply(Fun fun, std::vector<Term> terms) const = 0;
};

}  // namespace smt

#endif
