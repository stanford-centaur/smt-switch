
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

#include "datatype.h"
#include "exceptions.h"
#include "api/cpp/cvc5.h"

namespace smt {

  class Cvc5DatatypeDecl : public AbsDatatypeDecl {
    public :
    Cvc5DatatypeDecl(cvc5::api::DatatypeDecl t) : datatypedecl(t) {};
   protected:
    cvc5::api::DatatypeDecl datatypedecl;

  friend class Cvc5Solver;

  };

  class Cvc5DatatypeConstructorDecl : public AbsDatatypeConstructorDecl {
    public :
    Cvc5DatatypeConstructorDecl(cvc5::api::DatatypeConstructorDecl t) : datatypeconstructordecl(t) {};
    bool compare(const DatatypeConstructorDecl &) const override;

   protected:
    cvc5::api::DatatypeConstructorDecl datatypeconstructordecl;

  friend class Cvc5Solver;

  };


  class Cvc5Datatype : public AbsDatatype {
    public :
    Cvc5Datatype(cvc5::api::Datatype t) : datatype(t) {};
    std::string get_name() const override {
      return datatype.getName();
    }
    int get_num_constructors() const override {
      return datatype.getNumConstructors();
    }
    int get_num_selectors(std::string cons) const override {
      for (int i=0; i!=datatype.getNumConstructors();i++) {
        cvc5::api::DatatypeConstructor ct=datatype[i];
        if (ct.getName() == cons){
          return ct.getNumSelectors();}
      }
      throw InternalSolverException(datatype.getName()+"."+cons+" not found");
    }

   protected:
    cvc5::api::Datatype datatype;

  friend class Cvc5Solver;

  };




}

