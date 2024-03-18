#include "z3_datatype.h"

namespace z3 {
const bool operator==(const z3::sort & lhs, const z3::sort & rhs)
{
  return z3::eq(lhs, rhs);
}
const bool operator==(const z3::symbol & lhs, const z3::symbol & rhs)
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

}  // namespace smt
