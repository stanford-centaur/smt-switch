#include "datatype.h"

#include <cstddef>
#include <functional>

namespace smt {

AbsDatatypeDecl::~AbsDatatypeDecl() = default;

AbsDatatypeConstructorDecl::~AbsDatatypeConstructorDecl() = default;

std::size_t AbsDatatypeConstructorDecl::hash() const
{
  return std::hash<const AbsDatatypeConstructorDecl *>{}(this);
}

AbsDatatype::~AbsDatatype() = default;

std::size_t AbsDatatype::hash() const
{
  return std::hash<const AbsDatatype *>{}(this);
}

bool AbsDatatype::compare(const Datatype & d) const { return this == d.get(); }

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

// a null datatype equals only another null datatype
bool operator==(const Datatype & d1, const Datatype & d2)
{
  if (!d1 || !d2)
  {
    return !d1 && !d2;
  }
  return d1->compare(d2);
}

bool operator!=(const Datatype & d1, const Datatype & d2)
{
  return !(d1 == d2);
}

}  // namespace smt

namespace std {

size_t hash<smt::DatatypeConstructorDecl>::operator()(
    const smt::DatatypeConstructorDecl & d) const
{
  return d ? d->hash() : 0;
}

size_t hash<smt::Datatype>::operator()(const smt::Datatype & d) const
{
  return d ? d->hash() : 0;
}

}  // namespace std
