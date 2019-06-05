#ifndef SMT_OP_H
#define SMT_OP_H

#include <memory>
#include <vector>

#include "ops.h"
#include "sort.h"

namespace smt {

class AbsFun
{
 public:
  virtual ~AbsFun(){};
  virtual bool is_uf() const = 0;
  virtual bool is_op() const = 0;
  virtual Sort get_sort() const = 0;
  virtual Op get_op() const = 0;
  virtual std::string get_name() const = 0;
};

using Fun = std::shared_ptr<AbsFun>;
}  // namespace smt

#endif
