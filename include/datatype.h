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

#include "smt_defs.h"


namespace smt {

class AbsDatatypeDecl {

 public:
  AbsDatatypeDecl(){};
  virtual ~AbsDatatypeDecl(){};

};


class AbsDatatypeConstructorDecl {

 public:
  AbsDatatypeConstructorDecl(){};
  virtual ~AbsDatatypeConstructorDecl(){};
  virtual std::string get_name() const=0;
  virtual bool compare(const AbsDatatypeConstructorDecl & d) const=0;

};


class AbsDatatype {

 public:
  AbsDatatype(){};
  virtual ~AbsDatatype(){};
  virtual std::string get_name() const=0;
  virtual int get_num_selectors(std::string cons) const=0;
  virtual int get_num_constructors() const=0;
  virtual bool compare(const AbsDatatype & d) const=0;

};
bool operator==(const AbsDatatype& d1, const AbsDatatype& d2);
bool operator!=(const AbsDatatype& d1, const AbsDatatype& d2);

bool operator==(const AbsDatatypeConstructorDecl& d1, const AbsDatatypeConstructorDecl& d2);
bool operator!=(const AbsDatatypeConstructorDecl& d1, const AbsDatatypeConstructorDecl& d2);

}
