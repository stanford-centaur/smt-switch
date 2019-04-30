#ifndef SMT_SOLVER_H
#define SMT_SOLVER_H

#include <iostream>
#include <memory>
#include <string>

#include "exceptions.h"
#include "sort.h"
#include "term.h"

namespace smt
{
  // abstract class
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
    Sort construct_sort(Type t)
    {
      switch(t)
      {
      case INT: return IntSort();
        break;
      case REAL: return RealSort();
        break;
      default:
        throw IncorrectUsage(type2str[t]+" expects other arguments to construct_sort");
      }
    }
  };
}

#endif
