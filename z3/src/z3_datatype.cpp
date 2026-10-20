#include "z3_datatype.h"

#include <utility>

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
Z3DatatypeDecl::Z3DatatypeDecl(std::string n) : name(std::move(n)) {}

Z3DatatypeConstructorDecl::Z3DatatypeConstructorDecl(
    const std::shared_ptr<z3::context> & ctx, std::string name)
    : c(ctx), constructorname(std::move(name))
{
}

bool Z3DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & other) const
{
  auto cast = std::static_pointer_cast<Z3DatatypeConstructorDecl>(other);
  return std::tie(constructorname, fieldnames, sorts)
         == std::tie(cast->constructorname, cast->fieldnames, cast->sorts);
}

Z3Datatype::Z3Datatype(const std::shared_ptr<z3::context> & ctx, z3::sort s)
    : c(ctx), datatype(s)
{
}

std::string Z3Datatype::get_name() const { return datatype.name().str(); }

int Z3Datatype::get_num_constructors() const
{
  return Z3_get_datatype_sort_num_constructors(*c, datatype);
}

int Z3Datatype::get_num_selectors(std::string name) const
{
  for (int i = 0; i < get_num_constructors(); i++)
  {
    z3::func_decl cons{ *c, Z3_get_datatype_sort_constructor(*c, datatype, i) };
    if (cons.name().str() == name) return cons.arity();
  }
  throw IncorrectUsageException(datatype.name().str() + "." + name
                                + " not found");
}

}  // namespace smt
