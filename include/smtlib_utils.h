/*********************                                                        */
/*! \file smtlib_utils.h
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief SMT-LIB Utility functions.
**
**
**/

#pragma once

/* string macros for the SMT-LIB commands */
const std::string SET_OPTION_STR = "set-option";
const std::string SET_LOGIC_STR = "set-logic";
const std::string DECLARE_FUN_STR = "declare-fun";
const std::string DEFINE_FUN_STR = "define-fun";
const std::string DECLARE_SORT_STR = "declare-sort";
const std::string DEFINE_SORT_STR = "define-sort";
const std::string ASSERT_STR = "assert";
const std::string CHECK_SAT_STR = "check-sat";
const std::string CHECK_SAT_ASSUMING_STR = "check-sat-assuming";
const std::string GET_VALUE_STR = "get-value";
const std::string GET_UNSAT_ASSUMPTIONS_STR = "get-unsat-assumptions";
const std::string PUSH_STR = "push";
const std::string POP_STR = "pop";
const std::string RESET_ASSERTIONS_STR = "reset-assertions";
const std::string RESET_STR = "reset";
const std::string INTERPOLATION_GROUP_STR = "interpolation-group";
const std::string MSAT_GET_INTERPOLANT_STR = "get-interpolant";
const std::string CVC4_GET_INTERPOLANT_STR = "get-interpol";
