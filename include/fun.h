#ifndef SMT_FUN_H
#define SMT_FUN_H

#include <string>

#include "smt_defs.h"

namespace smt {

// TODO: Get rid of this!
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

}  // namespace smt

#endif
