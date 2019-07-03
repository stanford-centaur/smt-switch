#ifndef SMT_EXCEPTIONS_H
#define SMT_EXCEPTIONS_H

#include <exception>
#include <string>

/**
   Base exception for this codebase.

   All other exceptions used in the code should be derived
     classes of this.
 */

class SmtException : public std::exception
{
 public:
  /** Constructor (C strings).
   *  @param message C-style string error message.
   *                 The string contents are copied upon construction.
   *                 Hence, responsibility for deleting the char* lies
   *                 with the caller.
   */
  explicit SmtException(const char* message) : msg(message) {}

  /** Constructor (C++ STL strings).
   *  @param message The error message.
   */
  explicit SmtException(const std::string& message) : msg(message) {}

  /** Destructor.
   * Virtual to allow for subclassing.
   */
  virtual ~SmtException() throw() {}

  /** Returns a pointer to the (constant) error description.
   *  @return A pointer to a const char*. The underlying memory
   *          is in posession of the Exception object. Callers must
   *          not attempt to free the memory.
   */
  virtual const char* what() const throw() { return msg.c_str(); }

 protected:
  /** Error message.
   */
  std::string msg;
};

class IncorrectUsageException : public SmtException
{
 public:
  IncorrectUsageException(const char* msg) : SmtException(msg){};
};

class NotImplementedException : public SmtException
{
 public:
  NotImplementedException(const char* msg) : SmtException(msg){};
};

#endif
