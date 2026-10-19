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

#pragma once

#include <string>

#include "smt_defs.h"

namespace smt {

class AbsDatatypeDecl
{
 public:
  AbsDatatypeDecl() {};
  virtual ~AbsDatatypeDecl() {};
};

class AbsDatatypeConstructorDecl
{
 public:
  AbsDatatypeConstructorDecl() {};
  virtual ~AbsDatatypeConstructorDecl() {};
  virtual bool compare(const DatatypeConstructorDecl & d) const = 0;
};

class AbsDatatype
{
 public:
  AbsDatatype() {};
  virtual ~AbsDatatype() {};
  virtual std::string get_name() const = 0;
  virtual int get_num_selectors(std::string cons) const = 0;
  virtual int get_num_constructors() const = 0;
  /** The name of a constructor, by its position, counted from 0 */
  virtual std::string get_constructor_name(int i) const = 0;
  /** The name of a constructor's selector, by its position, counted from 0 */
  virtual std::string get_selector_name(std::string cons, int i) const = 0;
  /** The sort of a constructor's selector, by its position, counted from 0;
   *  the datatype's own sort for a selector declared with add_selector_self
   */
  virtual Sort get_selector_sort(std::string cons, int i) const = 0;
};
// Overloaded equivalence operators for two datatype constructor declarations
bool operator==(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2);
bool operator!=(const DatatypeConstructorDecl & d1,
                const DatatypeConstructorDecl & d2);
}  // namespace smt
