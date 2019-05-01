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
    AbsFunction(bool u, int a, BuiltinOp o)
      : uninterpreted(u), arity(a), op(o)
     {};
    virtual ~AbsFunction() {};
    unsigned int get_arity() const { return arity; };
    bool is_uf() const { return uninterpreted; };
    virtual std::vector<std::shared_ptr<AbsSort>> get_sorts() const = 0;
  protected:
    // whether this is an uninterpreted function
    // if not, then it's an indexed operator and op tells which kind
    bool uninterpreted;
    unsigned int arity;
    BuiltinOp op;
  };
}

#endif
