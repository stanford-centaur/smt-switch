#include "cvc5_datatype.h"
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

}  // namespace smt
