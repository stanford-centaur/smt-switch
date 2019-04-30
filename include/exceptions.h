#ifndef SMT_EXCEPTIONS_H
#define SMT_EXCEPTIONS_H

#include <exception>

class IncorrectUsage : public std::exception
{
 public:
   IncorrectUsage(const char * msg) : std::exception(msg) {};
}

#endif
