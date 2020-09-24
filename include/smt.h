/*********************                                                        */
/*! \file smt.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief The main include file for the smt-switch abstract interface.
**
**
**/

#pragma once

// Exceptions used by SMT API.
#include "exceptions.h"

// Class and smart pointer definitions.
#include "smt_defs.h"

// SMT-LIB Sort and Function operators.
#include "ops.h"

// Abstract sort interface.
#include "sort.h"

// Abstract term interface.
#include "term.h"

// Transfer terms between solvers.
#include "term_translator.h"

// Main solver interface.
#include "solver.h"

// Solver enums for identifying solver
#include "solver_enums.h"

