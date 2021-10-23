#include "cvc4_datatype.h"
namespace smt {

bool Cvc5DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<Cvc5DatatypeConstructorDecl> cd =
      std::static_pointer_cast<Cvc5DatatypeConstructorDecl>(d);
  return datatypeconstructordecl.toString()
         == cd->datatypeconstructordecl.toString();
}

}  // namespace smt
