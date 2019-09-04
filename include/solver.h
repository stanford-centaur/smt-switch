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
  virtual void set_opt(const std::string option, const bool value) const = 0;
  virtual void set_opt(const std::string option,
                       const std::string value) const = 0;
  virtual void set_logic(const std::string logic) const = 0;
  virtual void assert_formula(const Term& t) const = 0;
  virtual Result check_sat() const = 0;
  virtual Term get_value(Term& t) const = 0;
  // virtual bool check_sat_assuming() const = 0;
  virtual Sort make_sort(const std::string name, const unsigned int arity) const = 0;
  virtual Sort make_sort(const SortKind sk) const = 0;
  virtual Sort make_sort(const SortKind sk, const unsigned int size) const = 0;
  virtual Sort make_sort(const SortKind sk, const Sort idxsort, const Sort elemsort) const = 0;
  virtual Sort make_sort(const SortKind sk,
                         const std::vector<Sort> sorts,
                         const Sort sort) const = 0;
  /* make a boolean value term */
  virtual Term make_value(const bool b) const = 0;
  /* make an integer or bit-vector value term */
  virtual Term make_value(const unsigned int i, const Sort sort) const = 0;
  /* make a bit-vector, int, real or (in the future) string value term */
  virtual Term make_value(const std::string val, const Sort sort) const = 0;
  /* make a symbolic constant or function term */
  virtual Term make_term(const std::string name, const Sort sort) const = 0;
  /* build a new term */
  virtual Term make_term(const Op op, const Term t) const = 0;
  virtual Term make_term(const Op op, const Term t0, const Term t1) const = 0;
  virtual Term make_term(const Op op, const Term t0, const Term t1, const Term t2) const = 0;
  virtual Term make_term(const Op op, const std::vector<Term> terms) const = 0;
};

}  // namespace smt

#endif
