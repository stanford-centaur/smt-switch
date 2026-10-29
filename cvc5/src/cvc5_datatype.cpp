#include "cvc5_datatype.h"

#include <cstddef>
#include <memory>
#include <string>
#include <utility>

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
  return std::hash<std::string>{}(datatypeconstructordecl.toString());
}

bool Cvc5DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<Cvc5DatatypeConstructorDecl> cd =
      std::dynamic_pointer_cast<Cvc5DatatypeConstructorDecl>(d);
  return cd
         && datatypeconstructordecl.toString()
                == cd->datatypeconstructordecl.toString();
}

bool Cvc5DatatypeConstructorDecl::less(const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<Cvc5DatatypeConstructorDecl> cd =
      backend_pointer_cast<Cvc5DatatypeConstructorDecl>(d);
  return datatypeconstructordecl.toString()
         < cd->datatypeconstructordecl.toString();
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
