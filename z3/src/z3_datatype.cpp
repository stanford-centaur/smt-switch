#include "z3_datatype.h"

namespace z3 {
bool operator==(const z3::sort & lhs, const z3::sort & rhs)
{
  return z3::eq(lhs, rhs);
}
bool operator==(const z3::symbol & lhs, const z3::symbol & rhs)
{
  return lhs.str() == rhs.str();
}
}  // namespace z3

namespace smt {
bool Z3DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & other) const
{
  auto cast = std::static_pointer_cast<Z3DatatypeConstructorDecl>(other);
  return std::tie(constructorname, fieldnames, sorts)
         == std::tie(cast->constructorname, cast->fieldnames, cast->sorts);
}

std::string Z3Datatype::get_name() const { return datatype.name().str(); }

int Z3Datatype::get_num_constructors() const
{
  return Z3_get_datatype_sort_num_constructors(c, datatype);
}

int Z3Datatype::get_num_selectors(std::string name) const
{
  for (int i = 0; i < get_num_constructors(); i++)
  {
    z3::func_decl cons{ c, Z3_get_datatype_sort_constructor(c, datatype, i) };
    if (cons.name().str() == name) return cons.arity();
  }
  throw InternalSolverException(datatype.name().str() + "." + name
                                + " not found");
}

}  // namespace smt
