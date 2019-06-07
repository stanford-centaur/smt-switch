#ifndef SMT_OP_H
#define SMT_OP_H

#include <memory>
#include <string>

#include "ops.h"

namespace smt {
class AbsSort;
using Sort = std::shared_ptr<AbsSort>;

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
