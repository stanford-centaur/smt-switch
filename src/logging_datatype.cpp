/*!
 * \file logging_datatype.cpp
 * \brief Datatype declarations as a LoggingSolver records them.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "logging_datatype.h"

#include <memory>
#include <string>
#include <utility>

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

}  // namespace smt
