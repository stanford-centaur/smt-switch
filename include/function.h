#ifndef SMT_FUNCTION_H
#define SMT_FUNCTION_H

// TODO: remove the iostream headers when done debugging
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
     Abstract function class to be implemented by each supported solver.
   */
  class AbsFunction
  {
  public:
    AbsFunction(int a) : arity(a), op(o){};
    virtual ~AbsFunction() {};
    unsigned int get_arity() const { return arity; };
    // TODO remove this -- should be method on FunctionSort not Function
    /* virtual std::vector<Sort> get_domain_sorts() const = 0; */
    virtual Sort get_sort() const = 0;

  protected:
    unsigned int arity;
  };

  using Function = std::shared_ptr<AbsFunction>;
}

#endif
