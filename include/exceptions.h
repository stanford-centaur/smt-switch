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

class IncorrectUsageException : public SmtException
{
 public:
   IncorrectUsageException(const char * msg) : SmtException(msg) {};
}

class NotImplementedException(const char * msg) : SmtException(msg) {};

#endif
