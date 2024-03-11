#include "z3_datatype.h"

#include <memory>

#include "z3_sort.h"

const bool operator==(const z3::sort& lhs, const z3::sort& rhs) {
  return z3::eq(lhs, rhs);
}

namespace smt {
bool z3DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & other) const
{
  auto cast = std::static_pointer_cast<z3DatatypeConstructorDecl>(other);
  // FIXME: Compare the sorts and symbols!
  return std::tie(constructorname)
         == std::tie(cast->constructorname);
}

void z3DatatypeConstructorDecl::addField(std::string fn, const Sort & sort)
{
  fieldnames.push_back(c.str_symbol(fn.c_str()));
  sorts.push_back(std::static_pointer_cast<Z3Sort>(sort)->get_z3_type());
}

void z3DatatypeConstructorDecl::addSelfRef(std::string fn)
{
  fieldnames.push_back(c.str_symbol(fn.c_str()));
  sorts.emplace_back(c);  // push back an empty sort
}

}  // namespace smt
