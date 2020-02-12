#include "available_solvers.h"
#include "exceptions.h"

#if BUILD_BTOR
#include "boolector_factory.h"
#endif

#if BUILD_CVC4
#include "cvc4_factory.h"
#endif

#if BUILD_MSAT
#include "msat_factory.h"
#endif

using namespace smt;

namespace smt_tests
{

const CreateSolverFunsMap solvers({
    #if BUILD_BTOR
    {BTOR, BoolectorSolverFactory::create},
    #endif

    #if BUILD_CVC4
    {CVC4, CVC4SolverFactory::create},
    #endif

    #if BUILD_MSAT
    {MSAT, MsatSolverFactory::create},
    #endif
});


CreateSolverFunsMap available_solvers()
{
  return solvers;
}

std::ostream& operator<<(std::ostream& o, SolverEnum e)
{
  switch(e)
  {
  case BTOR: o << "BTOR"; break;
  case CVC4: o << "CVC4"; break;
  case MSAT: o << "MSAT"; break;
  default:
    // should print the integer representation
    throw NotImplementedException("Unknown SolverEnum: " + std::to_string(e));
    break;
  }

  return o;
}

}
