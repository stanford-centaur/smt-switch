#include "datatype.h"

namespace smt {
// Overloaded operators simply call the constructors' comparison functions
bool operator==(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2)
{
  return d1->compare(d2);
}
bool operator!=(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2)
{
  return !d1->compare(d2);
}

}  // namespace smt
