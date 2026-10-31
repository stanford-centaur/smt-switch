#include "cvc5_datatype.h"

#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <tuple>
#include <utility>

#include "cvc5_sort.h"
#include "exceptions.h"
#include "utils.h"

namespace smt {

Cvc5DatatypeDecl::Cvc5DatatypeDecl(cvc5::DatatypeDecl t) : datatypedecl(t) {}

std::string Cvc5DatatypeDecl::get_name() const
{
  return datatypedecl.getName();
}

Cvc5DatatypeConstructorDecl::Cvc5DatatypeConstructorDecl(
    cvc5::DatatypeConstructorDecl t, std::string n)
    : datatypeconstructordecl(t), name(std::move(n))
{
}

std::string Cvc5DatatypeConstructorDecl::get_name() const { return name; }

std::size_t Cvc5DatatypeConstructorDecl::hash() const
{
  // the parts compare checks: the name, the selector names and the selector
  // sorts
  std::size_t h = std::hash<std::string>{}(name);
  for (const std::pair<std::string, cvc5::Sort> & sel : selectors)
  {
    detail::hash_combine(h, sel.first);
    detail::hash_combine(h, sel.second);
  }
  return h;
}

bool Cvc5DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<Cvc5DatatypeConstructorDecl> cd =
      std::dynamic_pointer_cast<Cvc5DatatypeConstructorDecl>(d);
  return cd && std::tie(name, selectors) == std::tie(cd->name, cd->selectors);
}

bool Cvc5DatatypeConstructorDecl::less(const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<Cvc5DatatypeConstructorDecl> cd =
      backend_pointer_cast<Cvc5DatatypeConstructorDecl>(d);
  return std::tie(name, selectors) < std::tie(cd->name, cd->selectors);
}

namespace {

// The sort of a cvc5::Datatype is not directly accessible,
// but each constructor has it as its codomain.
cvc5::Sort sort_of(const cvc5::Datatype & dt)
{
  return dt[0].getTerm().getSort().getDatatypeConstructorCodomainSort();
}

}  // namespace

Cvc5Datatype::Cvc5Datatype(cvc5::Datatype t) : datatype(t) {}

int Cvc5Datatype::get_num_constructors() const
{
  return datatype.getNumConstructors();
}

int Cvc5Datatype::get_num_selectors(std::string cons) const
{
  for (size_t i = 0; i != datatype.getNumConstructors(); i++)
  {
    cvc5::DatatypeConstructor ct = datatype[i];
    if (ct.getName() == cons)
    {
      return ct.getNumSelectors();
    }
  }
  throw IncorrectUsageException(datatype.getName() + "." + cons + " not found");
}

std::vector<std::string> Cvc5Datatype::get_constructor_names() const
{
  std::vector<std::string> names;
  for (size_t i = 0; i != datatype.getNumConstructors(); i++)
  {
    names.push_back(datatype[i].getName());
  }
  return names;
}

std::vector<std::string> Cvc5Datatype::get_selector_names(
    const std::string & cons) const
{
  for (size_t i = 0; i != datatype.getNumConstructors(); i++)
  {
    cvc5::DatatypeConstructor ct = datatype[i];
    if (ct.getName() == cons)
    {
      std::vector<std::string> names;
      for (size_t j = 0; j != ct.getNumSelectors(); j++)
      {
        names.push_back(ct[j].getName());
      }
      return names;
    }
  }
  throw IncorrectUsageException(datatype.getName() + "." + cons + " not found");
}

Sort Cvc5Datatype::get_selector_sort(const std::string & cons,
                                     const std::string & sel) const
{
  for (size_t i = 0; i != datatype.getNumConstructors(); i++)
  {
    cvc5::DatatypeConstructor ct = datatype[i];
    if (ct.getName() != cons)
    {
      continue;
    }
    for (size_t j = 0; j != ct.getNumSelectors(); j++)
    {
      if (ct[j].getName() == sel)
      {
        return std::make_shared<Cvc5Sort>(ct[j].getCodomainSort());
      }
    }
    throw IncorrectUsageException(datatype.getName() + "." + cons + "." + sel
                                  + " not found");
  }
  throw IncorrectUsageException(datatype.getName() + "." + cons + " not found");
}

std::string Cvc5Datatype::get_name() const { return datatype.getName(); }

std::size_t Cvc5Datatype::hash() const
{
  return std::hash<cvc5::Sort>{}(sort_of(datatype));
}

bool Cvc5Datatype::compare(const Datatype & d) const
{
  // cvc5::Datatype's own == compares the copy each getDatatype makes, so
  // two Datatypes of one sort differ under it; the sort does not
  std::shared_ptr<Cvc5Datatype> other =
      std::dynamic_pointer_cast<Cvc5Datatype>(d);
  return other && sort_of(datatype) == sort_of(other->datatype);
}

bool Cvc5Datatype::less(const Datatype & d) const
{
  return sort_of(datatype)
         < sort_of(backend_pointer_cast<Cvc5Datatype>(d)->datatype);
}

}  // namespace smt
