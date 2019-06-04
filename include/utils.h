#ifndef SMT_UTILS_H
#define SMT_UTILS_H

#include <iostream>
#include "assert.h"

#ifdef _DEBUG
constexpr bool debug_mode = true;
constexpr bool assertion_mode = true;
#else
constexpr bool debug_mode = false;
constexpr bool assertion_mode = false;
#endif

#if defined(_ASSERTIONS) && !defined(_DEBUG)
constexpr bool assertion_mode = true;
#endif

#ifdef _LOGGING_LEVEL
constexpr std::size_t global_log_level = _LOGGING_LEVEL;
#else
constexpr std::size_t global_log_level = 0;
#endif

inline void Assert(bool assertion)
{
  if constexpr (assertion_mode)
  {
    assert(assertion);
  }
}

inline void Unreachable()
{
  if constexpr (assertion_mode)
  {
    assert(false);
  }
}

// logs to stdout
template <std::size_t lvl>
inline void Log(std::string msg)
{
  if constexpr (global_log_level >= lvl)
  {
    std::cout << msg << std::endl;
  }
}

#endif
