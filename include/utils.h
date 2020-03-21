#ifndef SMT_UTILS_H
#define SMT_UTILS_H

#include <iostream>
#include "assert.h"

#ifdef _DEBUG
#define _ASSERTIONS
#endif

#if defined(_ASSERTIONS) && !defined(_DEBUG)
bool assertion_mode = true;
#endif

#ifdef _LOGGING_LEVEL
const std::size_t global_log_level = _LOGGING_LEVEL;
#else
const std::size_t global_log_level = 0;
#endif

// TODO: Create an Assert with an optional message argument
inline void Assert(bool assertion)
{
  assert(assertion);
}

inline void Unreachable()
{
  assert(false);
}

// logs to stdout
template <std::size_t lvl>
inline void Log(std::string msg)
{
  if (global_log_level >= lvl)
  {
    std::cout << msg << std::endl;
  }
}

#endif
