
/*********************                                                        */
/*! \file cvc4_datatype.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief CVC4 implementation of AbsTerm
**
**
**/

#ifndef SMT_CVC4_DATATYPE_H
#define SMT_CVC4_DATATYPE_H

#include "datatype.h"
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




}
#endif
