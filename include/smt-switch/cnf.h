/*!
 * \file cnf.h
 * \brief Conversion of Boolean formulas to CNF and DIMACS
 * \author Bhaskar Gupta
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_CNF_H
#define SMT_SWITCH_CNF_H

#include <sstream>

#include "smt-switch/smt_defs.h"

namespace smt::cnf {

// Converts any boolean formula to cnf, formula is the formula to be converted
// to a cnf. Only the connectives not, and, or, xor, => and Boolean = are
// encoded; any other subterm, such as an ite or (bvult x y), is kept whole as
// an atom
Term convert(Term formula, SmtSolver s);

// Returns true if the formula is in cnf form, else false
bool is_cnf(Term formula);

/** Writes a CNF formula in DIMACS format
 *  @param cnf a Boolean term that is true or a conjunction of clauses, each
 *         a disjunction of symbols, negated symbols and false
 *  @param y the stream to write to
 *  @throws IncorrectUsageException if cnf is not Boolean or not in CNF
 */
void to_dimacs(const Term & cnf, std::ostringstream & y);

}  // namespace smt::cnf

#endif  // SMT_SWITCH_CNF_H
