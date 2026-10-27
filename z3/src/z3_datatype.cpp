#include "z3_datatype.h"

#include <algorithm>
#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <tuple>
#include <utility>

#include "exceptions.h"
#include "utils.h"

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

std::string Z3DatatypeDecl::get_name() const { return name; }

Z3DatatypeConstructorDecl::Z3DatatypeConstructorDecl(
    const std::shared_ptr<z3::context> & ctx, std::string name)
    : c(ctx), constructorname(std::move(name))
{
}

std::string Z3DatatypeConstructorDecl::get_name() const
{
  return constructorname;
}

std::size_t Z3DatatypeConstructorDecl::hash() const
{
  // the parts compare checks: the name, the field names and the field
  // sorts, by id. Boost's hash_combine: 0x9e3779b9 is 2^32 / golden ratio,
  // whose irregular bits spread the value; the shifts mix in the hash so
  // far, so the order of the parts matters and equal parts don't cancel out
  std::hash<std::string> str_hash;
  std::size_t h = str_hash(constructorname);
  for (const z3::symbol & field : fieldnames)
  {
    h ^= str_hash(field.str()) + 0x9e3779b9 + (h << 6) + (h >> 2);
  }
  for (const z3::sort & s : sorts)
  {
    h ^= s.id() + 0x9e3779b9 + (h << 6) + (h >> 2);
  }
  return h;
}

bool Z3DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & other) const
{
  auto cast = std::dynamic_pointer_cast<Z3DatatypeConstructorDecl>(other);
  return cast
         && std::tie(constructorname, fieldnames, sorts)
                == std::tie(
                    cast->constructorname, cast->fieldnames, cast->sorts);
}

bool Z3DatatypeConstructorDecl::less(const DatatypeConstructorDecl & d) const
{
  // The parts compare checks, in that order
  auto cast = backend_pointer_cast<Z3DatatypeConstructorDecl>(d);
  if (constructorname != cast->constructorname)
  {
    return constructorname < cast->constructorname;
  }
  if (!(fieldnames == cast->fieldnames))
  {
    return std::lexicographical_compare(
        fieldnames.begin(),
        fieldnames.end(),
        cast->fieldnames.begin(),
        cast->fieldnames.end(),
        [](const z3::symbol & a, const z3::symbol & b) {
          return a.str() < b.str();
        });
  }
  return std::lexicographical_compare(
      sorts.begin(),
      sorts.end(),
      cast->sorts.begin(),
      cast->sorts.end(),
      [](const z3::sort & a, const z3::sort & b) { return a.id() < b.id(); });
}

Z3Datatype::Z3Datatype(const std::shared_ptr<z3::context> & ctx, z3::sort s)
    : c(ctx), datatype(s)
{
}

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

std::string Z3Datatype::get_name() const { return datatype.name().str(); }

std::size_t Z3Datatype::hash() const { return datatype.id(); }

bool Z3Datatype::compare(const Datatype & d) const
{
  std::shared_ptr<Z3Datatype> other = std::dynamic_pointer_cast<Z3Datatype>(d);
  return other && z3::eq(datatype, other->datatype);
}

bool Z3Datatype::less(const Datatype & d) const
{
  // Ids are unique only within a context, so the context comes first.
  std::shared_ptr<Z3Datatype> other = backend_pointer_cast<Z3Datatype>(d);
  if (c != other->c)
  {
    return std::less<z3::context *>{}(c.get(), other->c.get());
  }
  return datatype.id() < other->datatype.id();
}

}  // namespace smt
