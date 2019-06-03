#ifndef SMT_UF_H
#define SMT_UF_H

#include <memory>
#include <string>
#include <vector>

#include "exceptions.h"
#include "sort.h"

namespace smt {
/**
   Abstract function class to be implemented by each supported solver.
 */
class AbsUF
{
 public:
  AbsUF(int a) : arity(a){};
  virtual ~AbsUF(){};
  unsigned int get_arity() const { return arity; };
  virtual Sort get_sort() const = 0;

 protected:
  unsigned int arity;
};

using UF = std::shared_ptr<AbsUF>;
}  // namespace smt

#endif
