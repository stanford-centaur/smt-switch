/*********************                                                        */
/*! \file solver_utils.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions for solver implementations. Meant for internal
**        use only, not from the API.
**
**/
#pragma once

#include <cstdint>
#include <string>

#include "ops.h"
#include "smt_defs.h"
#include "sort.h"
#include "term.h"

namespace smt {

/** Create distinctness constraint for each unique pair
 *  @param terms the vector of terms to make distinct
 *  @return the distinctness constraint
 */
Term make_distinct(const AbsSmtSolver * solver, const TermVec & terms);

/** Narrow an operator index to the 32 bits that most solver APIs take.
 *  Op stores indices as 64-bit, so without this the conversion is silent and
 *  a too-large index reaches the solver as an unrelated value.
 *  @param op the operator the index belongs to, used in the error message
 *  @param idx the index to narrow
 *  @return idx as a 32-bit value
 *  @throws IncorrectUsageException if idx does not fit
 */
std::uint32_t narrow_index(const Op & op, std::uint64_t idx);

/** Whether val is a number a value of sort kind sk, INT or REAL, can be
 *  made from, with an optional leading minus: a decimal numeral, or for a
 *  REAL also a decimal or a fraction of numerals. The slash of a fraction
 *  may have spaces around it, as TermTranslator writes one.
 *  Solvers read some other strings, such as "" or "1.2.3", without an
 *  error but not as the number meant, so check before handing one over.
 *  @param sk the sort kind of the value, INT or REAL
 *  @param val the string to check
 *  @return true iff val is such a number
 */
bool is_arith_number(SortKind sk, const std::string & val);

}  // namespace smt
