#include <unordered_map>

#include "cvc4_fun.h"

namespace smt {

bool CVC4Fun::is_uf() const {
  return uf;
}

bool CVC4Fun::is_op() const {
  return !uf;
}

bool CVC4Fun::is_prim_op() const
{
  return !uf & !indexed;
}

bool CVC4Fun::is_indexed() const
{
  return !uf & indexed;
}

Sort CVC4Fun::get_sort() const
{
  if (!uf)
    {
      throw IncorrectUsageException("Can't get sort for builtin operator.");
    }
  ::CVC4::api::Sort cs = fun.getSort();
  Sort s(new CVC4Sort(cs));
  return s;
}

Op CVC4Fun::get_op() const
{
  if (uf) {
    throw IncorrectUsageException("Can't get op from uninterpretd function.");
  }
  if (!indexed)
  {
    return Op(kind2primop[kind]);
  }
  else
  {
    PrimOp o = kind2primop[kind];
    if (o == Extract)
    {
      std::string rep = op.toString();
      std::string indices = rep.erase(0, rep.find(" ") + 1);
      indices = indices.erase(0, indices.find(" ") + 1);
      indices = indices.substr(0, indices.length()-1);
      std::size_t pos = indices.find(" ");
      std::string idx0 = indices.substr(0, pos);
      std::string idx1 = indices.substr(pos+1, idx1.length() - pos);
      return Op(Extract, std::atoi(idx0.c_str()), std::atoi(idx1.c_str()));
    }
    else
    {
      // TODO: Implement these
      throw NotImplementedException("Other indexed operators currently unimplemented.");
    }
  }
}

std::string CVC4Fun::get_name() const
{
  if (!uf)
    {
      throw IncorrectUsageException("Can't get name of builtin operator.");
    }
  return fun.toString();
}

}
