#include "boolector_fun.h"

namespace smt
{

/* BoolectorFun implementation */

BoolectorFun::~BoolectorFun()
{
  if (!contains_op)
    {
      boolector_release(btor, node);
    }
}

Sort BoolectorFun::get_sort() const
{
  if (!contains_op)
    {
      return sort;
    }
  else
    {
      throw IncorrectUsageException("Can't get sort from non-UF function.");
    }
}

Op BoolectorFun::get_op() const
{
  if (contains_op)
    {
      return op;
    }
  else
    {
      throw IncorrectUsageException("Can't get op from UF function");
    }
}

std::string BoolectorFun::get_name() const
{
  if (!contains_op)
    {
      const char * btor_symbol = boolector_get_symbol(btor, node);
      std::string symbol(btor_symbol);
      return symbol;
    }
  else
    {
      throw IncorrectUsageException("Can't get name from non-UF function.");
    }
}

/* end BoolectorFun implementation */

}
