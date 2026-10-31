/*!
 * \file logging_datatype.cpp
 * \brief Datatype declarations as a LoggingSolver records them.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "logging_datatype.h"

#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "exceptions.h"
#include "utils.h"

namespace smt {

LoggingDatatypeConstructorDecl::LoggingDatatypeConstructorDecl(
    DatatypeConstructorDecl wrapped, std::string n)
    : wrapped_decl(std::move(wrapped)), name(std::move(n))
{
}

std::string LoggingDatatypeConstructorDecl::get_name() const { return name; }

std::size_t LoggingDatatypeConstructorDecl::hash() const
{
  return std::hash<DatatypeConstructorDecl>{}(wrapped_decl);
}

bool LoggingDatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<LoggingDatatypeConstructorDecl> other =
      std::dynamic_pointer_cast<LoggingDatatypeConstructorDecl>(d);
  return other && wrapped_decl == other->wrapped_decl;
}

bool LoggingDatatypeConstructorDecl::less(
    const DatatypeConstructorDecl & d) const
{
  return wrapped_decl < backend_pointer_cast<LoggingDatatypeConstructorDecl>(d)
                            ->wrapped_decl;
}

LoggingDatatypeDecl::LoggingDatatypeDecl(DatatypeDecl wrapped, std::string n)
    : wrapped_decl(std::move(wrapped)), name(std::move(n))
{
}

std::string LoggingDatatypeDecl::get_name() const { return name; }

LoggingDatatype::LoggingDatatype(Datatype wrapped,
                                 Sort s,
                                 std::shared_ptr<LoggingDatatypeDecl> d)
    : wrapped_datatype(std::move(wrapped)),
      sort(std::move(s)),
      decl(std::move(d))
{
}

int LoggingDatatype::get_num_constructors() const
{
  return wrapped_datatype->get_num_constructors();
}

int LoggingDatatype::get_num_selectors(std::string cons) const
{
  return wrapped_datatype->get_num_selectors(std::move(cons));
}

std::vector<std::string> LoggingDatatype::get_constructor_names() const
{
  return wrapped_datatype->get_constructor_names();
}

std::vector<std::string> LoggingDatatype::get_selector_names(
    const std::string & cons) const
{
  return wrapped_datatype->get_selector_names(cons);
}

Sort LoggingDatatype::get_selector_sort(const std::string & cons,
                                        const std::string & sel) const
{
  for (const std::shared_ptr<LoggingDatatypeConstructorDecl> & con :
       decl->constructors)
  {
    if (con->name != cons)
    {
      continue;
    }
    for (const LoggingSelectorDecl & selector : con->selectors)
    {
      if (selector.name == sel)
      {
        return selector.sort ? selector.sort : sort;
      }
    }
    throw IncorrectUsageException("Constructor " + cons + " has no selector "
                                  + sel);
  }
  throw IncorrectUsageException("Constructor " + cons + " not found");
}

std::string LoggingDatatype::get_name() const
{
  return wrapped_datatype->get_name();
}

std::size_t LoggingDatatype::hash() const
{
  return std::hash<Datatype>{}(wrapped_datatype);
}

bool LoggingDatatype::compare(const Datatype & d) const
{
  std::shared_ptr<LoggingDatatype> other =
      std::dynamic_pointer_cast<LoggingDatatype>(d);
  return other && wrapped_datatype == other->wrapped_datatype;
}

bool LoggingDatatype::less(const Datatype & d) const
{
  return wrapped_datatype
         < backend_pointer_cast<LoggingDatatype>(d)->wrapped_datatype;
}

}  // namespace smt
