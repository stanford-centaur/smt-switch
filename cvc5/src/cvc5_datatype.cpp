#include "cvc5_datatype.h"

#include "exceptions.h"

namespace smt {

Cvc5DatatypeDecl::Cvc5DatatypeDecl(cvc5::DatatypeDecl t) : datatypedecl(t) {}

std::string Cvc5DatatypeDecl::get_name() const
{
  return datatypedecl.getName();
}

Cvc5DatatypeConstructorDecl::Cvc5DatatypeConstructorDecl(
    cvc5::DatatypeConstructorDecl t)
    : datatypeconstructordecl(t)
{
}

bool Cvc5DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<Cvc5DatatypeConstructorDecl> cd =
      std::static_pointer_cast<Cvc5DatatypeConstructorDecl>(d);
  return datatypeconstructordecl.toString()
         == cd->datatypeconstructordecl.toString();
}

Cvc5Datatype::Cvc5Datatype(cvc5::Datatype t) : datatype(t) {}

std::string Cvc5Datatype::get_name() const { return datatype.getName(); }

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

}  // namespace smt
