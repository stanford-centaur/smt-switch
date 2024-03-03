#include "z3_datatype.h"

#include <memory>
#include "z3_sort.h"

namespace smt {
bool z3DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & other) const
{
  auto cast = std::static_pointer_cast<z3DatatypeConstructorDecl>(other);
  return std::tie(name, names, sorts)
         == std::tie(cast->name, cast->names, cast->sorts);
}

void z3DatatypeConstructorDecl::addField(std::string fn, const Sort & sort)
{
  names.push_back(fn);
  sorts.push_back(sort);
}

void z3DatatypeConstructorDecl::addSelfRef(std::string fn)
{
  names.push_back(fn);
  auto sort = (c.datatype_sort(c.str_symbol(name.c_str())));
  sorts.push_back(std::make_shared<Z3Sort>(sort, c));
}

}  // namespace smt
