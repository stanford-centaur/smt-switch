/*********************                                                        */
/*! \file utils.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions.
**
**
**/

#pragma once

#include <iostream>
#include "assert.h"

#include "smt.h"

#ifndef NDEBUG
#define _ASSERTIONS
#endif

#if !defined(NDEBUG) || defined(_ASSERTIONS)
#define Assert(EX) (void)((EX) || (__assert(#EX, __FILE__, __LINE__), 0))
#define Unreachable() \
  (void)((__assert("location should be unreachable", __FILE__, __LINE__), 0))
#else
#define Assert(EX)
#define Unreachable()
#endif

#ifdef _LOGGING_LEVEL
const std::size_t global_log_level = _LOGGING_LEVEL;
#else
const std::size_t global_log_level = 0;
#endif

// logs to stdout
template <std::size_t lvl>
inline void Log(std::string msg)
{
  if (global_log_level >= lvl)
  {
    std::cout << msg << std::endl;
  }
}

namespace smt {

// term helper methods
void op_partition(smt::PrimOp o, const smt::Term & term, smt::TermVec & out);

void conjunctive_partition(const smt::Term & term,
                           smt::TermVec & out,
                           bool include_bvand = false);

void disjunctive_partition(const smt::Term & term,
                           smt::TermVec & out,
                           bool include_bvor = false);

void get_free_symbolic_consts(const smt::Term &term, smt::TermVec &out);

}  // namespace smt
