#ifndef SMT_SMT_H
#define SMT_SMT_H

#include <memory>
#include <string>
#include <vector>

#include "exceptions.h"
#include "fun.h"
#include "sort.h"
#include "term.h"

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
  virtual Term make_const(unsigned int i, Sort sort) const = 0;
  virtual Fun make_fun(Op op) const = 0;
  virtual void assert_formula(const Term& t) const = 0;
  virtual bool check_sat() const = 0;
  virtual Term get_value(Term& t) const = 0;
  // virtual bool check_sat_assuming() const = 0;
  virtual Sort make_sort(Kind k) const = 0;
  virtual Sort make_sort(Kind k, unsigned int size) const = 0;
  virtual Sort make_sort(Kind k, Sort idxsort, Sort elemsort) const = 0;
  virtual Sort make_sort(Kind k, std::vector<Sort> sorts, Sort sort) const = 0;
  virtual Term apply(Op op, Term t) const = 0;
  virtual Term apply(Op op, Term t0, Term t1) const = 0;
  virtual Term apply(Op op, Term t0, Term t1, Term t2) const = 0;
  virtual Term apply(Op op, std::vector<Term> terms) const = 0;
  virtual Term apply(Fun fun, Term t) const = 0;
  virtual Term apply(Fun fun, Term t0, Term t1) const = 0;
  virtual Term apply(Fun fun, Term t0, Term t1, Term t2) const = 0;
  virtual Term apply(Fun fun, std::vector<Term> terms) const = 0;
};

using SmtSolver = std::unique_ptr<AbsSmtSolver>;

}  // namespace smt

#endif
