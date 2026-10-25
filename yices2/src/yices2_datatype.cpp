/*!
 * \file yices2_datatype.cpp
 * \brief Yices2 implementation of the datatype interfaces, for enumerations.
 * \author Po-Chun Chien
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "yices2_datatype.h"

#include <yices.h>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <utility>

#include "exceptions.h"
#include "utils.h"

namespace smt {

Yices2DatatypeConstructorDecl::Yices2DatatypeConstructorDecl(std::string n)
    : name(std::move(n))
{
}

std::string Yices2DatatypeConstructorDecl::get_name() const { return name; }

// With no selectors, the name is all a constructor has, so it alone is
// hashed, compared and ordered.

std::size_t Yices2DatatypeConstructorDecl::hash() const
{
  return std::hash<std::string>{}(name);
}

bool Yices2DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<Yices2DatatypeConstructorDecl> other =
      std::dynamic_pointer_cast<Yices2DatatypeConstructorDecl>(d);
  return other && name == other->name;
}

bool Yices2DatatypeConstructorDecl::less(
    const DatatypeConstructorDecl & d) const
{
  return name < backend_pointer_cast<Yices2DatatypeConstructorDecl>(d)->name;
}

Yices2DatatypeDecl::Yices2DatatypeDecl(std::string n) : name(std::move(n)) {}

std::string Yices2DatatypeDecl::get_name() const { return name; }

Yices2Datatype::Yices2Datatype(type_t t) : type(t) {}

int Yices2Datatype::get_num_constructors() const
{
  return static_cast<int>(yices_scalar_type_card(type));
}

int Yices2Datatype::get_num_selectors(std::string cons) const
{
  if (get_constant(cons) == NULL_TERM)
  {
    throw IncorrectUsageException(get_name() + "." + cons + " not found");
  }
  return 0;
}

std::string Yices2Datatype::get_name() const
{
  const char * name = yices_get_type_name(type);
  if (name == nullptr)
  {
    throw InternalSolverException("Yices2 scalar type has no name");
  }
  return name;
}

// A datatype is its scalar type. Every Yices2 solver shares the one Yices
// instance, so type ids are unique across them.

std::size_t Yices2Datatype::hash() const { return type; }

bool Yices2Datatype::compare(const Datatype & d) const
{
  std::shared_ptr<Yices2Datatype> other =
      std::dynamic_pointer_cast<Yices2Datatype>(d);
  return other && type == other->type;
}

bool Yices2Datatype::less(const Datatype & d) const
{
  return type < backend_pointer_cast<Yices2Datatype>(d)->type;
}

term_t Yices2Datatype::get_constant(const std::string & cons) const
{
  const uint32_t card = yices_scalar_type_card(type);
  for (uint32_t i = 0; i < card; ++i)
  {
    // the same term each time: Yices hash-conses its constants
    term_t constant = yices_constant(type, static_cast<int32_t>(i));
    const char * name = yices_get_term_name(constant);
    if (name != nullptr && cons == name)
    {
      return constant;
    }
  }
  return NULL_TERM;
}

}  // namespace smt
