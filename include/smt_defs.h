/*********************                                                        */
/*! \file smt_defs.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Type definitions for pointers to main abstract objects.
**
**
**/

#pragma once

#include <memory>

#include "my_ptr.h"

namespace smt {

struct Op;

class AbsSort;
using Sort = my_ptr<AbsSort>;

class AbsTerm;
using Term = my_ptr<AbsTerm>;

class AbsSmtSolver;
using SmtSolver = std::shared_ptr<AbsSmtSolver>;

// Datatype theory related
class AbsDatatypeDecl;
using DatatypeDecl = std::shared_ptr<AbsDatatypeDecl>;

class AbsDatatypeConstructorDecl;
using DatatypeConstructorDecl = std::shared_ptr<AbsDatatypeConstructorDecl>;

class AbsDatatype;
using Datatype = std::shared_ptr<AbsDatatype>;

template <typename _Tp, typename... _Args>
inline my_ptr<_Tp> make_my_ptr(_Args &&... __args)
{
  // adapted the make_shared function
  // typedef typename std::remove_const<_Tp>::type _Tp_nc;
  // return allocate_shared<_Tp>(std::allocator<_Tp_nc>(),
  //                             std::forward<_Args>(__args)...);
#ifdef USE_SHARED_PTR
  return std::make_shared<_Tp>(std::forward<_Args>(__args)...);
#else
  return my_ptr<_Tp>(new _Tp(std::forward<_Args>(__args)...));
#endif
}

}  // namespace smt

