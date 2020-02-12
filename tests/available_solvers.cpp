#include "available_solvers.h"

#if BUILD_BTOR
#include "boolector_factory.h"
#endif

#if BUILD_CVC4
#include "cvc4_factory.h"
#endif

#if BUILD_MSAT
#include "msat_factory.h"
#endif

namespace smt
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

}
