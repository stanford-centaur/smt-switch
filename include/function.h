#ifndef SMT_FUNCTION_H
#define SMT_FUNCTION_H

// TODO: remove the iostream headers when done debugging
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "exceptions.h"
#include "sort.h"
#include "term.h"

// TODO If possible, AbsFunction should be able to represent constructed functions as well
//      e.g. bitvector extract
//      then the union can just be builtin operators or functions

namespace smt
{
  /**
     Abstract function class to be implemented by each supported solver.
   */
  class AbsFunction
  {
  public:
    AbsFunction(unsigned int a, std::vector<std::shared_ptr<AbsSort>> s)
      : arity(a), sorts(s)
      {};
    virtual ~AbsFunction() {};
  protected:
    unsigned int arity;
    std::vector<std::shared_ptr<AbsSort>> sorts;
  }
}

#endif
