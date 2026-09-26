#include <gtest/gtest.h>

#include <exception>
#include <string>

#include "exceptions.h"

// Callers catch SmtException, or std::exception, to handle any error the
// library raises, so every exception class must be catchable as both and
// keep its message.
template <typename E>
class UnitExceptions : public ::testing::Test
{
};

using ExceptionTypes = ::testing::Types<SmtException,
                                        IncorrectUsageException,
                                        NotImplementedException,
                                        InternalSolverException>;
TYPED_TEST_SUITE(UnitExceptions, ExceptionTypes);

TYPED_TEST(UnitExceptions, CaughtAsSmtException)
{
  EXPECT_THROW(throw TypeParam("test"), SmtException);
}

TYPED_TEST(UnitExceptions, CaughtAsStdException)
{
  EXPECT_THROW(throw TypeParam("test"), std::exception);
}

TYPED_TEST(UnitExceptions, MessageFromCString)
{
  TypeParam e("from a C string");
  EXPECT_STREQ(e.what(), "from a C string");
}

TYPED_TEST(UnitExceptions, MessageFromStdString)
{
  TypeParam e(std::string("from a std::string"));
  EXPECT_STREQ(e.what(), "from a std::string");
}

TYPED_TEST(UnitExceptions, MessageThroughBaseReference)
{
  try
  {
    throw TypeParam("through the base");
  }
  catch (const std::exception & e)
  {
    EXPECT_STREQ(e.what(), "through the base");
    return;
  }
  FAIL() << "exception was not caught as std::exception";
}
