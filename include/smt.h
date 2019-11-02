#ifndef SMT_SMT_H
#define SMT_SMT_H

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

#endif
