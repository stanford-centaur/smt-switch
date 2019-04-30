#ifndef SMT_EXCEPTIONS_H
#define SMT_EXCEPTIONS_H

#include <exception>

/**
   Base exception for this codebase.

   All other exceptions used in the code should be derived
     classes of this.
 */
class SmtException : public std::exception
{
 public:
   SmtException(const char * msg) : std::exception(msg) {};
}

class IncorrectUsage : public SmtException
{
 public:
   IncorrectUsage(const char * msg) : SmtException(msg) {};
}

#endif
