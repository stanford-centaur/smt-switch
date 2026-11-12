/*!
 * \file cvc5_interpolator.cpp
 * \brief cvc5 implementation of AbsSmtInterpolator
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/cvc5_interpolator.h"

#include <cvc5/cvc5.h>

#include <memory>
#include <string>

#include "smt-switch/cvc5_solver.h"
#include "smt-switch/cvc5_term.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/term.h"
#include "smt-switch/utils.h"

namespace smt {

Cvc5Interpolator::Cvc5Interpolator()
    : AbsSmtInterpolator(CVC5_INTERPOLATOR, std::make_shared<Cvc5Solver>()),
      cvc5_solver(std::static_pointer_cast<Cvc5Solver>(backend_solver))
{
  initialize();
}

void Cvc5Interpolator::initialize()
{
  // set_opt refuses produce-interpolants, so this is the only place it is set
  cvc5_solver->set_opt("produce-interpolants", "true");
  // each query is asked between a push and a pop, which need it
  cvc5_solver->set_opt("incremental", "true");
}

// incremental never gets here, so cvc5's own option stays on
void Cvc5Interpolator::do_set_opt(const std::string & option,
                                  const std::string & value)
{
  if (option == "produce-interpolants")
  {
    throw IncorrectUsageException(
        "The cvc5 interpolator does not allow the option " + option);
  }
  cvc5_solver->set_opt(option, value);
}

// cvc5 interpolates between its assertions and a given formula, so A is
// asserted and the interpolant asked for not B. cvc5 synthesizes the
// interpolant. It finds none both when A and B are satisfiable and when its
// search gives up. On a satisfiable query, the search may also run on without
// end, so A and B are checked first.
Result Cvc5Interpolator::compute_interpolant(const Term & A,
                                             const Term & B,
                                             Term & out_I) const
{
  std::shared_ptr<cvc5::Solver> solver = cvc5_solver->get_cvc5_solver();
  ::cvc5::Term notB =
      std::static_pointer_cast<Cvc5Term>(make_term(Not, B))->term;
  Result r;
  ::cvc5::Term I;
  solver->push();
  try
  {
    solver->assertFormula(backend_pointer_cast<Cvc5Term>(A)->term);
    r = cvc5_solver->check_sat_assuming(TermVec{ B });
    // an interpolant proves unsat, so one is still worth asking for when
    // the check answers unknown
    if (!r.is_sat())
    {
      I = solver->getInterpolant(notB);
    }
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    solver->pop();
    throw InternalSolverException(e.what());
  }
  catch (...)
  {
    // check_sat_assuming has already turned cvc5's exceptions into ours
    solver->pop();
    throw;
  }
  solver->pop();
  if (r.is_sat())
  {
    return r;
  }
  if (I.isNull())
  {
    std::string explanation = "cvc5 found no interpolant";
    if (r.is_unknown())
    {
      explanation +=
          ", and the satisfiability check of A and B answered unknown: "
          + r.get_explanation();
    }
    return Result(UNKNOWN, explanation);
  }
  out_I = std::make_shared<Cvc5Term>(I);
  return Result(UNSAT);
}

Result Cvc5Interpolator::compute_seq_interpolants(const TermVec & formulae,
                                                  TermVec & out_I) const
{
  return sequence_from_interpolants(formulae, out_I);
}

}  // namespace smt
