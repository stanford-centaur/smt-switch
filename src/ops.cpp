#include "ops.h"

namespace smt
{

std::string to_string(PrimOp op)
{
  return std::string(primop2str[op]);
}

bool operator==(Op o1, Op o2)
{
  if (o1.prim_op != o2.prim_op)
    {
      return false;
    }
  else if (o1.num_idx != o2.num_idx)
    {
      return false;
    }
  else
    {
      return (o1.num_idx == 0) || ((o1.num_idx == 1) && (o1.idx0 == o2.idx0))
        || ((o1.num_idx == 2) && (o1.idx0 == o2.idx0)
            && (o1.idx1 == o2.idx1));
    }
}

bool operator!=(Op o1, Op o2)
{
  if (o1.prim_op != o2.prim_op)
    {
      return true;
    }
  else if (o1.num_idx != o2.num_idx)
    {
      return true;
    }
  else
    {
      return ((o1.num_idx > 1) || (o1.idx0 != o2.idx0))
        && ((o1.num_idx != 2) || (o1.idx0 != o2.idx0)
            || (o1.idx1 != o2.idx1));
    }
}

std::ostream& operator<<(std::ostream& output, const Op o)
{
  output << "(" << ::smt::to_string(o.prim_op);
  if (o.num_idx > 0)
    {
      output << " " << o.idx0;
    }
  if (o.num_idx == 2)
    {
      output << " " << o.idx1;
    }
  output << ")";
  return output;
}

}
