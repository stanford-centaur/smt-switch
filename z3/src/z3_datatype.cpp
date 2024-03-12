#include "z3_datatype.h"

#include <memory>

#include "z3++.h"
#include "z3_sort.h"

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

void Z3DatatypeConstructorDecl::addField(std::string fn, const Sort & sort)
{
  fieldnames.push_back(c.str_symbol(fn.c_str()));
  sorts.push_back(std::static_pointer_cast<Z3Sort>(sort)->get_z3_type());
}

void Z3DatatypeConstructorDecl::addSelfRef(std::string fn)
{
  fieldnames.push_back(c.str_symbol(fn.c_str()));
  sorts.emplace_back(c);  // push back an empty sort because we don't know the datatype name yet
}

}  // namespace smt
