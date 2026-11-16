/*!
 * \file z3_datatype.cpp
 * \brief Z3 implementations of the datatype interfaces
 * \author Tung-Che Chang
 * \author Áron Ricardo Perez-Lopez
 * \date 2024
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/z3_datatype.h"

#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <utility>

#include "smt-switch/exceptions.h"
#include "smt-switch/solver_utils.h"
#include "smt-switch/z3_sort.h"

namespace smt {

namespace {

// Orders sorts by id, with a null sort, which has no id, first
bool sort_less(const z3::sort & lhs, const z3::sort & rhs)
{
  if (static_cast<Z3_sort>(lhs) == nullptr
      || static_cast<Z3_sort>(rhs) == nullptr)
  {
    return static_cast<Z3_sort>(lhs) == nullptr
           && static_cast<Z3_sort>(rhs) != nullptr;
  }
  return lhs.id() < rhs.id();
}

}  // namespace

Z3DatatypeDecl::Z3DatatypeDecl(std::string n) : name(std::move(n)) {}

std::string Z3DatatypeDecl::get_name() const { return name; }

Z3DatatypeConstructorDecl::Z3DatatypeConstructorDecl(
    const std::shared_ptr<Z3Context> & ctx, std::string name)
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
  // sorts, by id
  std::size_t h = std::hash<std::string>{}(constructorname);
  for (const std::pair<std::string, z3::sort> & sel : selectors)
  {
    // a self selector's null sort has no id
    std::size_t sort_id =
        static_cast<Z3_sort>(sel.second) == nullptr ? 0 : sel.second.id();
    backend::hash_combine(h, sel.first);
    backend::hash_combine(h, sort_id);
  }
  return h;
}

bool Z3DatatypeConstructorDecl::compare(const DatatypeConstructorDecl & d) const
{
  auto other = std::dynamic_pointer_cast<Z3DatatypeConstructorDecl>(d);
  if (!other || constructorname != other->constructorname
      || selectors.size() != other->selectors.size())
  {
    return false;
  }
  for (std::size_t i = 0; i < selectors.size(); ++i)
  {
    const auto & [name, sort] = selectors[i];
    const auto & [other_name, other_sort] = other->selectors[i];
    if (name != other_name || !z3::eq(sort, other_sort))
    {
      return false;
    }
  }
  return true;
}

bool Z3DatatypeConstructorDecl::less(const DatatypeConstructorDecl & d) const
{
  auto other = backend::pointer_cast<Z3DatatypeConstructorDecl>(d);
  if (constructorname != other->constructorname)
  {
    return constructorname < other->constructorname;
  }
  // the selectors in order, each by name and then by sort
  for (std::size_t i = 0; i < selectors.size() && i < other->selectors.size();
       ++i)
  {
    const auto & [name, sort] = selectors[i];
    const auto & [other_name, other_sort] = other->selectors[i];
    if (name != other_name)
    {
      return name < other_name;
    }
    if (sort_less(sort, other_sort))
    {
      return true;
    }
    if (sort_less(other_sort, sort))
    {
      return false;
    }
  }
  return selectors.size() < other->selectors.size();
}

Z3Datatype::Z3Datatype(const std::shared_ptr<Z3Context> & ctx, z3::sort s)
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
  auto other = backend::pointer_cast<Z3Datatype>(d);
  if (c != other->c)
  {
    return std::less<Z3Context *>{}(c.get(), other->c.get());
  }
  return datatype.id() < other->datatype.id();
}

}  // namespace smt
