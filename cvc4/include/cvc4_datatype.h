
/*********************                                                        */
/*! \file cvc4_datatype.h
** \verbatim
** Top contributors (to current version):
**   Kristopher Brown
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Thin wrapper for CVC4 Datatype-related classes.
**/

#pragma once

#include "datatype.h"
#include "exceptions.h"
#include "api/cvc4cpp.h"

namespace smt {

  class CVC4DatatypeDecl : public AbsDatatypeDecl {
    public :
    CVC4DatatypeDecl(CVC4::api::DatatypeDecl t) : datatypedecl(t) {};
   protected:
    CVC4::api::DatatypeDecl datatypedecl;

  friend class CVC4Solver;

  };

  class CVC4DatatypeConstructorDecl : public AbsDatatypeConstructorDecl {
    public :
    CVC4DatatypeConstructorDecl(CVC4::api::DatatypeConstructorDecl t) : datatypeconstructordecl(t) {};
   protected:
    CVC4::api::DatatypeConstructorDecl datatypeconstructordecl;

  friend class CVC4Solver;

  };


  class CVC4Datatype : public AbsDatatype {
    public :
    CVC4Datatype(CVC4::api::Datatype t) : datatype(t) {};
    std::string get_name() const override {
      return datatype.getName();
    }
    int get_num_constructors() const override {
      return datatype.getNumConstructors();
    }
    int get_num_selectors(std::string cons) const override {
      for (int i=0; i!=datatype.getNumConstructors();i++) {
        CVC4::api::DatatypeConstructor ct=datatype[i];
        if (ct.getName() == cons){
          return ct.getNumSelectors();}
      }
      throw InternalSolverException(datatype.getName()+"."+cons+" not found");
    }

   protected:
    CVC4::api::Datatype datatype;

  friend class CVC4Solver;

  };




}

