#include "cvc4_datatype.h"
namespace smt {

bool CVC4DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<CVC4DatatypeConstructorDecl> cd =
      std::static_pointer_cast<CVC4DatatypeConstructorDecl>(d);
  return datatypeconstructordecl.toString()
         == cd->datatypeconstructordecl.toString();
}

}  // namespace smt
