/*!
 * \file logging_datatype.h
 * \brief Datatype declarations as a LoggingSolver records them.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * A logging solver hands these out in place of the wrapped solver's own
 * declarations. They remember each constructor and selector, so that the
 * constructor, selector and tester terms of the datatype can be given
 * logging sorts.
 */

#pragma once

#include <cstddef>
#include <memory>
#include <string>
#include <vector>

#include "datatype.h"
#include "smt_defs.h"

namespace smt {

/** A selector as declared: its name, and its logging sort, which is null
 *  for one declared with add_selector_self */
struct LoggingSelectorDecl
{
  std::string name;
  Sort sort;
};

class LoggingDatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  LoggingDatatypeConstructorDecl(DatatypeConstructorDecl wrapped,
                                 std::string n);
  std::string get_name() const override;
  std::size_t hash() const override;
  bool compare(const DatatypeConstructorDecl & d) const override;
  bool less(const DatatypeConstructorDecl & d) const override;

 protected:
  DatatypeConstructorDecl wrapped_decl;  ///< the underlying declaration
  std::string name;
  std::vector<LoggingSelectorDecl> selectors;

  friend class LoggingSolver;
};

class LoggingDatatypeDecl : public AbsDatatypeDecl
{
 public:
  LoggingDatatypeDecl(DatatypeDecl wrapped, std::string n);
  std::string get_name() const override;

 protected:
  DatatypeDecl wrapped_decl;  ///< the underlying declaration
  std::string name;
  std::vector<std::shared_ptr<LoggingDatatypeConstructorDecl>> constructors;

  friend class LoggingSolver;
};

}  // namespace smt
