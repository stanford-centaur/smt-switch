/*!
 * \file solver_factory.cpp
 * \brief Creating a solver or interpolator from its solver enum
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * A shared libsmt-switch does not link the backends, which link it, so it
 * finds each one when asked: among the libraries already loaded, then
 * beside libsmt-switch, then on the system's search path. A static one is
 * linked with every backend it was built with and refers to them directly.
 */
#include "smt-switch/solver_factory.h"

#ifdef SMT_SWITCH_LOAD_BACKENDS
#include <dlfcn.h>
#endif

#include <string>
#include <vector>
#ifdef SMT_SWITCH_LOAD_BACKENDS
#include <filesystem>
#endif

#include "smt-switch/exceptions.h"

namespace smt {

namespace {

/* The backend whose library is libsmt-switch-<suffix>, loaded if it is not
 * yet and kept loaded, since its solvers run its code. Loading it again
 * only finds the library already loaded. A static libsmt-switch loads
 * none.
 */
[[maybe_unused]] const backend::Factory & load_backend(
    const std::string & suffix)
{
#ifdef SMT_SWITCH_LOAD_BACKENDS
  // an object in libsmt-switch, for dladdr to name the file that holds it
  static constexpr char library_locator = 0;
  const std::string entry = "smt_switch_backend_" + suffix;
  const std::string file = SMT_SWITCH_LIBRARY_PREFIX "smt-switch-" + suffix
                           + SMT_SWITCH_LIBRARY_SUFFIX;
  // a backend the program links, or one loaded already
  void * symbol = dlsym(RTLD_DEFAULT, entry.c_str());
  if (!symbol)
  {
    void * handle = nullptr;
    Dl_info info;
    if (dladdr(&library_locator, &info) && info.dli_fname)
    {
      std::filesystem::path beside =
          std::filesystem::path(info.dli_fname).parent_path() / file;
      if (std::filesystem::exists(beside))
      {
        handle = dlopen(beside.c_str(), RTLD_NOW | RTLD_LOCAL);
        if (!handle)
        {
          throw SystemException("Could not load " + beside.string() + ": "
                                + dlerror());
        }
      }
    }
    if (!handle)
    {
      handle = dlopen(file.c_str(), RTLD_NOW | RTLD_LOCAL);
      if (!handle)
      {
        throw NotImplementedException(
            "The " + suffix + " backend is not available: " + dlerror());
      }
    }
    symbol = dlsym(handle, entry.c_str());
    if (!symbol)
    {
      throw SystemException(file + " does not provide " + entry + ": "
                            + dlerror());
    }
  }
  return *static_cast<const backend::Factory *>(symbol);
#else
  throw NotImplementedException("smt-switch was built without the " + suffix
                                + " backend");
#endif
}

/* The backend of a solver or its interpolator */
const backend::Factory & factory_for(SolverEnum se)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (se)
  {
    case BTOR:
#ifdef SMT_SWITCH_STATIC_BACKEND_BTOR
      return backend::smt_switch_backend_btor;
#else
      return load_backend("btor");
#endif
    case BZLA:
    case BZLA_INTERPOLATOR:
#ifdef SMT_SWITCH_STATIC_BACKEND_BITWUZLA
      return backend::smt_switch_backend_bitwuzla;
#else
      return load_backend("bitwuzla");
#endif
    case CVC5:
    case CVC5_INTERPOLATOR:
#ifdef SMT_SWITCH_STATIC_BACKEND_CVC5
      return backend::smt_switch_backend_cvc5;
#else
      return load_backend("cvc5");
#endif
    case MSAT:
    case MSAT_INTERPOLATOR:
#ifdef SMT_SWITCH_STATIC_BACKEND_MSAT
      return backend::smt_switch_backend_msat;
#else
      return load_backend("msat");
#endif
    case YICES2:
    case YICES2_INTERPOLATOR:
#ifdef SMT_SWITCH_STATIC_BACKEND_YICES2
      return backend::smt_switch_backend_yices2;
#else
      return load_backend("yices2");
#endif
    case Z3:
#ifdef SMT_SWITCH_STATIC_BACKEND_Z3
      return backend::smt_switch_backend_z3;
#else
      return load_backend("z3");
#endif
    case GENERIC_SOLVER:
      throw IncorrectUsageException(
          "A generic solver needs a solver binary; construct a GenericSolver "
          "instead");
  }
  throw InternalException("Unknown SolverEnum: " + std::to_string(se));
}

}  // namespace

SmtSolver solvers::create(SolverEnum se, bool logging)
{
  if (is_interpolator_solver_enum(se))
  {
    throw IncorrectUsageException(to_string(se)
                                  + " is an interpolator; use "
                                    "interpolators::create");
  }
  return factory_for(se).create(logging);
}

SmtInterpolator interpolators::create(SolverEnum se)
{
  if (!is_interpolator_solver_enum(se))
  {
    throw IncorrectUsageException(to_string(se)
                                  + " is not an interpolator; use "
                                    "solvers::create");
  }
  const backend::Factory & factory = factory_for(se);
  if (!factory.create_interpolator)
  {
    throw NotImplementedException("This build of " + to_string(se)
                                  + " cannot interpolate");
  }
  return factory.create_interpolator();
}

std::vector<SolverEnum> solvers::available()
{
  std::vector<SolverEnum> available;
  for (SolverEnum se : { BTOR, BZLA, CVC5, MSAT, YICES2, Z3 })
  {
    try
    {
      factory_for(se);
      available.push_back(se);
    }
    catch (const NotImplementedException &)
    {
    }
  }
  return available;
}

std::vector<SolverEnum> interpolators::available()
{
  std::vector<SolverEnum> available;
  for (SolverEnum se : { BZLA_INTERPOLATOR,
                         CVC5_INTERPOLATOR,
                         MSAT_INTERPOLATOR,
                         YICES2_INTERPOLATOR })
  {
    // creating one is the only way to tell whether a backend's build can
    // interpolate
    try
    {
      create(se);
      available.push_back(se);
    }
    catch (const NotImplementedException &)
    {
    }
  }
  return available;
}

}  // namespace smt
