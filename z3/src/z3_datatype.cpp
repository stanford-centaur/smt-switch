#include "z3_datatype.h"

#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <tuple>
#include <utility>

#include "exceptions.h"
#include "utils.h"
#include "z3_sort.h"

namespace z3 {

bool operator==(const z3::sort & lhs, const z3::sort & rhs)
{
  return z3::eq(lhs, rhs);
}
// A null sort, which has no id, comes first
bool operator<(const z3::sort & lhs, const z3::sort & rhs)
{
  if (static_cast<Z3_sort>(lhs) == nullptr
      || static_cast<Z3_sort>(rhs) == nullptr)
  {
    return static_cast<Z3_sort>(lhs) == nullptr
           && static_cast<Z3_sort>(rhs) != nullptr;
  }
  return lhs.id() < rhs.id();
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
  // the parts compare checks: the name, the selector names and the selector
  // sorts, by id. Boost's hash_combine: 0x9e3779b9 is 2^32 / golden ratio,
  // whose irregular bits spread the value; the shifts mix in the hash so
  // far, so the order of the parts matters and equal parts don't cancel out
  std::hash<std::string> str_hash;
  std::size_t h = str_hash(constructorname);
  for (const std::pair<std::string, z3::sort> & sel : selectors)
  {
    // a self selector's null sort has no id
    std::size_t sort_id =
        static_cast<Z3_sort>(sel.second) == nullptr ? 0 : sel.second.id();
    h ^= str_hash(sel.first) + 0x9e3779b9 + (h << 6) + (h >> 2);
    h ^= sort_id + 0x9e3779b9 + (h << 6) + (h >> 2);
  }
  return h;
}

bool Z3DatatypeConstructorDecl::compare(const DatatypeConstructorDecl & d) const
{
  auto other = std::dynamic_pointer_cast<Z3DatatypeConstructorDecl>(d);
  return other
         && std::tie(constructorname, selectors)
                == std::tie(other->constructorname, other->selectors);
}

bool Z3DatatypeConstructorDecl::less(const DatatypeConstructorDecl & d) const
{
  auto other = backend_pointer_cast<Z3DatatypeConstructorDecl>(d);
  return std::tie(constructorname, selectors)
         < std::tie(other->constructorname, other->selectors);
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

std::vector<std::string> Z3Datatype::get_constructor_names() const
{
  std::vector<std::string> names;
  for (int i = 0; i < get_num_constructors(); i++)
  {
    z3::func_decl cons{ *c, Z3_get_datatype_sort_constructor(*c, datatype, i) };
    names.push_back(cons.name().str());
  }
  return names;
}

std::vector<std::string> Z3Datatype::get_selector_names(
    const std::string & cons) const
{
  for (int i = 0; i < get_num_constructors(); i++)
  {
    z3::func_decl con{ *c, Z3_get_datatype_sort_constructor(*c, datatype, i) };
    if (con.name().str() == cons)
    {
      std::vector<std::string> names;
      for (const z3::func_decl & sel : con.accessors())
      {
        names.push_back(sel.name().str());
      }
      return names;
    }
  }
  throw IncorrectUsageException(datatype.name().str() + "." + cons
                                + " not found");
}

Sort Z3Datatype::get_selector_sort(const std::string & cons,
                                   const std::string & sel) const
{
  for (int i = 0; i < get_num_constructors(); i++)
  {
    z3::func_decl con{ *c, Z3_get_datatype_sort_constructor(*c, datatype, i) };
    if (con.name().str() != cons)
    {
      continue;
    }
    for (const z3::func_decl & accessor : con.accessors())
    {
      if (accessor.name().str() == sel)
      {
        return std::make_shared<Z3Sort>(c, accessor.range());
      }
    }
    throw IncorrectUsageException(datatype.name().str() + "." + cons + "." + sel
                                  + " not found");
  }
  throw IncorrectUsageException(datatype.name().str() + "." + cons
                                + " not found");
}

std::string Z3Datatype::get_name() const { return datatype.name().str(); }

std::size_t Z3Datatype::hash() const { return datatype.id(); }

bool Z3Datatype::compare(const Datatype & d) const
{
  auto other = std::dynamic_pointer_cast<Z3Datatype>(d);
  return other && z3::eq(datatype, other->datatype);
}

bool Z3Datatype::less(const Datatype & d) const
{
  // Ids are unique only within a context, so the context comes first.
  auto other = backend_pointer_cast<Z3Datatype>(d);
  if (c != other->c)
  {
    return std::less<z3::context *>{}(c.get(), other->c.get());
  }
  return datatype.id() < other->datatype.id();
}

}  // namespace smt
