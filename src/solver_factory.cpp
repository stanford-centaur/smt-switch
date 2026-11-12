/*!
 * \file solver_factory.cpp
 * \brief Creating a solver or interpolator from its kind
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
const backend::Factory & factory_for(solvers::Kind kind)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (kind)
  {
    case solvers::BTOR:
#ifdef SMT_SWITCH_STATIC_BACKEND_BTOR
      return backend::smt_switch_backend_btor;
#else
      return load_backend("btor");
#endif
    case solvers::BZLA:
#ifdef SMT_SWITCH_STATIC_BACKEND_BITWUZLA
      return backend::smt_switch_backend_bitwuzla;
#else
      return load_backend("bitwuzla");
#endif
    case solvers::CVC5:
#ifdef SMT_SWITCH_STATIC_BACKEND_CVC5
      return backend::smt_switch_backend_cvc5;
#else
      return load_backend("cvc5");
#endif
    case solvers::MSAT:
#ifdef SMT_SWITCH_STATIC_BACKEND_MSAT
      return backend::smt_switch_backend_msat;
#else
      return load_backend("msat");
#endif
    case solvers::YICES2:
#ifdef SMT_SWITCH_STATIC_BACKEND_YICES2
      return backend::smt_switch_backend_yices2;
#else
      return load_backend("yices2");
#endif
    case solvers::Z3:
#ifdef SMT_SWITCH_STATIC_BACKEND_Z3
      return backend::smt_switch_backend_z3;
#else
      return load_backend("z3");
#endif
    case solvers::GENERIC:
      throw IncorrectUsageException(
          "A generic solver needs a solver binary; construct a GenericSolver "
          "instead");
  }
  throw InternalException("Unknown solver kind: " + to_string(kind));
}

}  // namespace

SmtSolver solvers::create(Kind kind, bool logging)
{
  return factory_for(kind).create(logging);
}

SmtInterpolator interpolators::create(Kind kind)
{
  const backend::Factory & factory = factory_for(solver_kind(kind));
  if (!factory.create_interpolator)
  {
    throw NotImplementedException("This build of " + to_string(kind)
                                  + " cannot interpolate");
  }
  return factory.create_interpolator();
}

std::vector<solvers::Kind> solvers::available()
{
  std::vector<Kind> available;
  for (Kind kind : { BTOR, BZLA, CVC5, MSAT, YICES2, Z3 })
  {
    try
    {
      factory_for(kind);
      available.push_back(kind);
    }
    catch (const NotImplementedException &)
    {
    }
  }
  return available;
}

std::vector<interpolators::Kind> interpolators::available()
{
  std::vector<Kind> available;
  for (Kind kind : { BZLA, CVC5, MSAT, YICES2 })
  {
    // creating one is the only way to tell whether a backend's build can
    // interpolate
    try
    {
      create(kind);
      available.push_back(kind);
    }
    catch (const NotImplementedException &)
    {
    }
  }
  return available;
}

}  // namespace smt
