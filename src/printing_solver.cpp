/*********************                                                        */
/*! \file printing_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that wraps another SmtSolver and tracks the term DAG by
**        wrapping sorts and terms and performs hash-consing.
**
**/

#include "printing_solver.h"
#include "utils.h"


#define SET_OPTION_STR "set-option"
#define SET_LOGIC_STR "set-logic"
#define DECLARE_FUN_STR "declare-fun"
#define DECLARE_SORT_STR "declare-sort"
#define ASSERT_STR "assert"
#define CHECK_SAT_STR "check-sat"
#define CHECK_SAT_ASSUMING_STR "check-sat-assuming"
#define GET_VALUE_STR "get-value"
#define GET_UNSAT_ASSUMPTIONS_STR "get-unsat-assumptions"
#define PUSH_STR "push"
#define POP_STR "pop"
#define RESET_ASSERTIONS_STR "reset-assertions"
#define RESET_STR "reset"
#define INTERPOLATION_GROUP_STR "interpolation-group"
#define MSAT_GET_INTERPOLANT_STR "get-interpolant"

using namespace std;

namespace smt {

/* PrintingSolver */

// implementations

}  // namespace smt
