/*********************                                                        */
/*! \file datatype.h
** \verbatim
** Top contributors (to current version):
**   Kristopher Brown
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Abstract interface for SMT datatypes.
**
**
**/

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#pragma once

#include <cstddef>
#include <string>
#include <vector>

#include "smt_defs.h"

namespace smt {

class AbsDatatypeDecl
{
 public:
  // defined in the .cpp to anchor the vtable
  virtual ~AbsDatatypeDecl();
  virtual std::string get_name() const = 0;
};

class AbsDatatypeConstructorDecl
{
 public:
  // defined in the .cpp to anchor the vtable
  virtual ~AbsDatatypeConstructorDecl();
  virtual std::string get_name() const = 0;
  virtual std::size_t hash() const;
  virtual bool compare(const DatatypeConstructorDecl & d) const = 0;
  virtual bool less(const DatatypeConstructorDecl & d) const;
};

class AbsDatatype
{
 public:
  // defined in the .cpp to anchor the vtable
  virtual ~AbsDatatype();
  virtual int get_num_constructors() const = 0;
  virtual int get_num_selectors(std::string cons) const = 0;
  /** The names of the constructors, in the order they were declared
   *
   *  The solver's get_constructor and get_tester take these names.
   */
  virtual std::vector<std::string> get_constructor_names() const = 0;
  /** The names of the selectors of a constructor, in the order they were
   *  declared
   *
   *  The solver's get_selector takes these names.
   *  @param cons the name of the constructor
   *  @throws IncorrectUsageException if the datatype has no constructor cons
   */
  virtual std::vector<std::string> get_selector_names(
      const std::string & cons) const = 0;
  /** The sort of a selector, the datatype's own sort for one declared with
   *  add_selector_self
   *
   *  With the names, these sorts describe the whole declaration: a
   *  constructor's sort maps its selectors' sorts to the datatype, and a
   *  tester's maps the datatype to Bool.
   *  @param cons the name of the constructor
   *  @param sel the name of the selector
   *  @throws IncorrectUsageException if the datatype has no constructor cons,
   *  or cons has no selector sel
   */
  virtual Sort get_selector_sort(const std::string & cons,
                                 const std::string & sel) const = 0;
  virtual std::string get_name() const = 0;
  virtual std::size_t hash() const;
  virtual bool compare(const Datatype & d) const;
  virtual bool less(const Datatype & d) const;
};

// Overloaded equivalence operators for two datatype constructor declarations
bool operator==(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2);
bool operator!=(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2);
// Ordered by class, then by less, with a null declaration first
bool operator<(const DatatypeConstructorDecl & d1,
               const DatatypeConstructorDecl & d2);
bool operator>(const DatatypeConstructorDecl & d1,
               const DatatypeConstructorDecl & d2);
bool operator<=(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2);
bool operator>=(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2);

// Same operators for datatypes themselves
bool operator==(const Datatype & d1, const Datatype & d2);
bool operator!=(const Datatype & d1, const Datatype & d2);
bool operator<(const Datatype & d1, const Datatype & d2);
bool operator>(const Datatype & d1, const Datatype & d2);
bool operator<=(const Datatype & d1, const Datatype & d2);
bool operator>=(const Datatype & d1, const Datatype & d2);

}  // namespace smt
