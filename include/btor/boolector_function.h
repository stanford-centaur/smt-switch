#include <memory>
#include <utility>
#include <vector>

#include "function.h"
#include "ops.h"

#include "boolector/boolector.h"

namespace smt
{
  class BoolectorFunction : AbsFunction
  {
  public:
    BoolectorFunction(Btor* b, BoolectorNode * n,
                      std::vector<std::shared_ptr<AbsSort>> sorts,
                      std::shared_ptr<AbsSort> sort)
      : AbsFunction(sorts.size()), btor(b), node(n), sorts(sorts), sort(sort) {};
    virtual std::vector<std::shared_ptr>> get_sorts() const override
    {
      return sorts;
    }
  protected:
    Btor * btor;
    BoolectorNode * node;
    std::vector<std::shared_ptr<AbsSort>> sorts;
    std::shared_ptr<AbsSort> sort;
  };
}
