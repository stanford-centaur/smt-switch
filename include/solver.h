#ifndef SMT_SOLVER_H
#define SMT_SOLVER_H

#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "exceptions.h"
#include "ops.h"
#include "sort.h"
#include "term.h"

namespace smt
{
  /**
     Abstract solver class to be implemented by each supported solver.
   */
  class AbsSolver
  {
  public:
    AbsSolver() {};
    virtual ~AbsSolver() {};
    virtual Sort declare_sort(const std::string name, unsigned int arity) const = 0;
    virtual Term declare_const(const std::string name, Sort sort) const = 0;
    // virtual Function declare_fun(const std::string name,
    //                              const std::vector<Sort>& sorts,
    //                              Sort sort) const = 0;
    virtual void assert(Term& t) const = 0;
    virtual bool check_sat() const = 0;
    Term get_value(Term& t) const = 0;
    // virtual bool check_sat_assuming() const = 0;
    std::shared_ptr<AbsSort> construct_sort(Type t) const = 0;
    std::shared_ptr<AbsSort> construct_sort(Type t,
                                            unsigned int size) const = 0;
    std::shared_ptr<AbsSort> construct_sort(Type t,
                                            std::shared_ptr<AbsSort> idxsort,
                                            std::shared_ptr<AbsSort> elemsort) const = 0;
    std::shared_ptr<AbsTerm> apply_op(BuiltinOp op,
                                      std::vector<std::shared_ptr<AbsTerm>> terms) const = 0;
    std::shared_ptr<AbsTerm> apply_op(Op op,
                                      std::vector<std::shared_ptr<AbsTerm>> terms) const = 0;
  };
}

#endif
