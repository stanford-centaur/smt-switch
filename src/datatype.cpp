#include "datatype.h"

#include <cstddef>
#include <functional>
#include <typeindex>
#include <typeinfo>

namespace smt {

AbsDatatypeDecl::~AbsDatatypeDecl() = default;

AbsDatatypeConstructorDecl::~AbsDatatypeConstructorDecl() = default;

std::size_t AbsDatatypeConstructorDecl::hash() const
{
  return std::hash<const AbsDatatypeConstructorDecl *>{}(this);
}

bool AbsDatatypeConstructorDecl::less(const DatatypeConstructorDecl & d) const
{
  return std::less<const AbsDatatypeConstructorDecl *>{}(this, d.get());
}

AbsDatatype::~AbsDatatype() = default;

std::size_t AbsDatatype::hash() const
{
  return std::hash<const AbsDatatype *>{}(this);
}

bool AbsDatatype::compare(const Datatype & d) const { return this == d.get(); }

bool AbsDatatype::less(const Datatype & d) const
{
  return std::less<const AbsDatatype *>{}(this, d.get());
}

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

// Declarations of different classes never compare equal, so they order by
// class, and less sees only its own. Handles of two solvers of one backend
// never compare equal either, but can tie on every key here, so the order is
// consistent only among the handles of one solver and its wrappers.
bool operator<(const DatatypeConstructorDecl & d1,
               const DatatypeConstructorDecl & d2)
{
  if (!d1 || !d2)
  {
    return !d1 && d2;
  }
  const auto & o1 = *d1;
  const auto & o2 = *d2;
  std::type_index t1 = typeid(o1);
  std::type_index t2 = typeid(o2);
  if (t1 != t2)
  {
    return t1 < t2;
  }
  return d1->less(d2);
}
bool operator>(const DatatypeConstructorDecl & d1,
               const DatatypeConstructorDecl & d2)
{
  return d2 < d1;
}
bool operator<=(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2)
{
  return !(d2 < d1);
}
bool operator>=(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2)
{
  return !(d1 < d2);
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

// As for declarations: by class, then by less
bool operator<(const Datatype & d1, const Datatype & d2)
{
  if (!d1 || !d2)
  {
    return !d1 && d2;
  }
  const auto & o1 = *d1;
  const auto & o2 = *d2;
  std::type_index t1 = typeid(o1);
  std::type_index t2 = typeid(o2);
  if (t1 != t2)
  {
    return t1 < t2;
  }
  return d1->less(d2);
}
bool operator>(const Datatype & d1, const Datatype & d2) { return d2 < d1; }
bool operator<=(const Datatype & d1, const Datatype & d2) { return !(d2 < d1); }
bool operator>=(const Datatype & d1, const Datatype & d2) { return !(d1 < d2); }

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
