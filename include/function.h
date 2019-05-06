#ifndef SMT_FUNCTION_H
#define SMT_FUNCTION_H

// TODO: remove the iostream headers when done debugging
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "exceptions.h"
#include "sort.h"

namespace smt
{
  /**
     Abstract function class to be implemented by each supported solver.
   */
  class AbsFunction
  {
  public:
    AbsFunction(int a) : arity(a) {};
    virtual ~AbsFunction() {};
    unsigned int get_arity() const { return arity; };
    virtual Sort get_sort() const = 0;

  protected:
    unsigned int arity;
  };

  using Function = std::shared_ptr<AbsFunction>;
}

#endif
