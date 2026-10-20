/*!
 * \file logging_datatype.cpp
 * \brief Datatype declarations as a LoggingSolver records them.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "logging_datatype.h"

#include <cstddef>
#include <memory>
#include <string>
#include <utility>

#include "exceptions.h"

namespace smt {

LoggingDatatypeConstructorDecl::LoggingDatatypeConstructorDecl(
    DatatypeConstructorDecl wrapped, std::string name)
    : wrapped_decl(std::move(wrapped)), name(std::move(name))
{
}

bool LoggingDatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<LoggingDatatypeConstructorDecl> other =
      std::dynamic_pointer_cast<LoggingDatatypeConstructorDecl>(d);
  return other && wrapped_decl == other->wrapped_decl;
}

LoggingDatatypeDecl::LoggingDatatypeDecl(DatatypeDecl wrapped, std::string name)
    : wrapped_decl(std::move(wrapped)), name(std::move(name))
{
}

LoggingDatatype::LoggingDatatype(Datatype wrapped,
                                 Sort sort,
                                 std::shared_ptr<LoggingDatatypeDecl> decl)
    : wrapped_datatype(std::move(wrapped)),
      sort(std::move(sort)),
      decl(std::move(decl))
{
}

std::string LoggingDatatype::get_name() const
{
  return wrapped_datatype->get_name();
}

int LoggingDatatype::get_num_selectors(std::string cons) const
{
  return wrapped_datatype->get_num_selectors(cons);
}

int LoggingDatatype::get_num_constructors() const
{
  return wrapped_datatype->get_num_constructors();
}

std::string LoggingDatatype::get_constructor_name(int i) const
{
  return wrapped_datatype->get_constructor_name(i);
}

std::string LoggingDatatype::get_selector_name(std::string cons, int i) const
{
  return wrapped_datatype->get_selector_name(cons, i);
}

Sort LoggingDatatype::get_selector_sort(std::string cons, int i) const
{
  for (const std::shared_ptr<LoggingDatatypeConstructorDecl> & con :
       decl->constructors)
  {
    if (con->name == cons && i >= 0
        && static_cast<std::size_t>(i) < con->selectors.size())
    {
      const Sort & s = con->selectors[i].sort;
      return s ? s : sort;
    }
  }
  throw IncorrectUsageException(get_name() + "." + cons + " has no selector "
                                + std::to_string(i));
}

}  // namespace smt
