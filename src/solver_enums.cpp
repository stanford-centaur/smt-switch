#include <iostream>
#include <sstream>
#include <unordered_map>

#include "exceptions.h"
#include "solver_enums.h"

using namespace std;

namespace smt {

const unordered_map<SolverEnum, unordered_set<SolverAttribute>>
    solver_attributes({
        { BTOR, { TERMITER, ARRAY_MODELS, CONSTARR, UNSAT_CORE } },

        { BTOR_LOGGING,
          { LOGGING,
            TERMITER,
            ARRAY_MODELS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE } },

        { CVC4,
          {
              TERMITER,
              THEORY_INT,
              // TODO: put this back after getStoreAllBase() is in API
              // ARRAY_MODELS,
              CONSTARR,
              FULL_TRANSFER,
              UNSAT_CORE,
              THEORY_DATATYPE,
          } },

        { CVC4_LOGGING,
          { LOGGING,
            TERMITER,
            THEORY_INT,
            // TODO: put this back after getStoreAllBase() is in API
            // ARRAY_MODELS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE } },

        { MSAT,
          { TERMITER,
            THEORY_INT,
            ARRAY_MODELS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE } },

        { MSAT_LOGGING,
          { LOGGING,
            TERMITER,
            THEORY_INT,
            ARRAY_MODELS,
            CONSTARR,
            FULL_TRANSFER,
            UNSAT_CORE } },

        // TODO: Yices2 should support UNSAT_CORE
        //       but something funky happens with testing
        //       has something to do with the context and yices_init
        //       look into this more and re-enable it
        { YICES2, { THEORY_INT } },

        { YICES2_LOGGING,
          { LOGGING, TERMITER, THEORY_INT, FULL_TRANSFER, UNSAT_CORE } },

    });

bool solver_has_attribute(SolverEnum se, SolverAttribute sa)
{
  unordered_set<SolverAttribute> solver_attrs = get_solver_attributes(se);
  return solver_attrs.find(sa) != solver_attrs.end();
}

std::unordered_set<SolverAttribute> get_solver_attributes(SolverEnum se)
{
  if (solver_attributes.find(se) == solver_attributes.end())
  {
    throw NotImplementedException("Unhandled solver enum: " + to_string(se));
  }

  return solver_attributes.at(se);
}

std::ostream & operator<<(std::ostream & o, SolverEnum e)
{
  switch (e)
  {
    case BTOR: o << "BTOR"; break;
    case CVC4: o << "CVC4"; break;
    case MSAT: o << "MSAT"; break;
    case YICES2: o << "YICES2"; break;
    case BTOR_LOGGING: o << "BTOR_LOGGING"; break;
    case CVC4_LOGGING: o << "CVC4_LOGGING"; break;
    case MSAT_LOGGING: o << "MSAT_LOGGING"; break;
    case YICES2_LOGGING: o << "YICES2_LOGGING"; break;
    default:
      // should print the integer representation
      throw NotImplementedException("Unknown SolverEnum: " + std::to_string(e));
      break;
  }

  return o;
}

std::string to_string(SolverEnum e)
{
  ostringstream ostr;
  ostr << e;
  return ostr.str();
}

}  // namespace smt
