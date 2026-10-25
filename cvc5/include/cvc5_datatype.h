
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

#include "cvc5/cvc5.h"
#include "datatype.h"
#include "exceptions.h"

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
  explicit Cvc5DatatypeConstructorDecl(cvc5::DatatypeConstructorDecl t);
  bool compare(const DatatypeConstructorDecl &) const override;

 protected:
  cvc5::DatatypeConstructorDecl datatypeconstructordecl;

  friend class Cvc5Solver;
};

class Cvc5Datatype : public AbsDatatype
{
 public:
  explicit Cvc5Datatype(cvc5::Datatype t);
  std::string get_name() const override { return datatype.getName(); }
  int get_num_constructors() const override
  {
    return datatype.getNumConstructors();
  }
  int get_num_selectors(std::string cons) const override
  {
    for (size_t i = 0; i != datatype.getNumConstructors(); i++)
    {
      cvc5::DatatypeConstructor ct = datatype[i];
      if (ct.getName() == cons)
      {
        return ct.getNumSelectors();
      }
    }
    throw IncorrectUsageException(datatype.getName() + "." + cons
                                  + " not found");
  }

 protected:
  cvc5::Datatype datatype;

  friend class Cvc5Solver;
};

}  // namespace smt
