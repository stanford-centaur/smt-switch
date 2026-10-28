
/*********************                                                        */
/*! \file cvc5_datatype.h
** \verbatim
** Top contributors (to current version):
**   Kristopher Brown
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Thin wrapper for cvc5 Datatype-related classes.
**/

#pragma once

#include <cvc5/cvc5.h>

#include <cstddef>
#include <string>

#include "datatype.h"

namespace smt {

class Cvc5DatatypeDecl : public AbsDatatypeDecl
{
 public:
  explicit Cvc5DatatypeDecl(cvc5::DatatypeDecl t);
  std::string get_name() const override;

 protected:
  cvc5::DatatypeDecl datatypedecl;

  friend class Cvc5Solver;
};

class Cvc5DatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  Cvc5DatatypeConstructorDecl(cvc5::DatatypeConstructorDecl t, std::string n);
  std::string get_name() const override;
  std::size_t hash() const override;
  bool compare(const DatatypeConstructorDecl &) const override;
  bool less(const DatatypeConstructorDecl & d) const override;

 protected:
  cvc5::DatatypeConstructorDecl datatypeconstructordecl;
  // cvc5's declaration cannot be asked for its name
  std::string name;

  friend class Cvc5Solver;
};

class Cvc5Datatype : public AbsDatatype
{
 public:
  explicit Cvc5Datatype(cvc5::Datatype t);
  int get_num_constructors() const override;
  int get_num_selectors(std::string cons) const override;
  std::string get_name() const override;
  std::size_t hash() const override;
  bool compare(const Datatype & d) const override;
  bool less(const Datatype & d) const override;

 protected:
  cvc5::Datatype datatype;

  friend class Cvc5Solver;
};

}  // namespace smt
