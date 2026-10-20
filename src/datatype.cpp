#include "datatype.h"

namespace smt {
// Overloaded operators call the constructors' comparison functions; a null
// declaration equals only another null declaration
bool operator==(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2)
{
  if (!d1 || !d2)
  {
    return !d1 && !d2;
  }
  return d1->compare(d2);
}
bool operator!=(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2)
{
  return !(d1 == d2);
}

}  // namespace smt
