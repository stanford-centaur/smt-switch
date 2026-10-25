/*!
 * \file yices2-datatypes.cpp
 * \brief Yices2's datatypes, which are enumerations made as scalar types.
 * \author Po-Chun Chien
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * What every backend with ENUM_DATATYPE does is checked in test-dt.cpp.
 * These are the parts particular to Yices2: what it refuses, and that its
 * global names do not mix up two declarations of one datatype. Unwrapped,
 * as the logging solver would catch some of the misuse itself.
 */

#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"
#include "yices2_factory.h"

using namespace smt;

namespace {

/** Declares the datatype `name` with a constructor of each of `values` */
Sort declare_enum(const SmtSolver & s,
                  const std::string & name,
                  const std::vector<std::string> & values)
{
  DatatypeDecl decl = s->make_datatype_decl(name);
  for (const std::string & value : values)
  {
    s->add_constructor(decl, s->make_datatype_constructor_decl(value));
  }
  return s->make_sort(decl);
}

TEST(Yices2Datatypes, RefusesSelectors)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  DatatypeConstructorDecl cons = s->make_datatype_constructor_decl("cons");
  EXPECT_THROW(s->add_selector(cons, "head", s->make_sort(INT)),
               NotImplementedException);
  EXPECT_THROW(s->add_selector_self(cons, "tail"), NotImplementedException);
}

TEST(Yices2Datatypes, RefusesEmptyAndRepeatedConstructors)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  EXPECT_THROW(declare_enum(s, "Empty", {}), IncorrectUsageException);
  EXPECT_THROW(declare_enum(s, "Twice", { "a", "b", "a" }),
               IncorrectUsageException);
}

TEST(Yices2Datatypes, RefusesMisappliedConstructorsAndTesters)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort color = declare_enum(s, "Color", { "red", "green" });
  Sort light = declare_enum(s, "Light", { "on", "off" });
  Term red = s->get_constructor(color, "red");
  Term x = s->make_symbol("x", light);

  EXPECT_THROW(s->make_term(Apply_Constructor, red, x),
               IncorrectUsageException);
  EXPECT_THROW(s->make_term(Apply_Constructor, x), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Apply_Tester, s->get_tester(color, "red"), x),
               IncorrectUsageException);
  EXPECT_THROW(s->make_term(Apply_Tester, x, x), IncorrectUsageException);
}

// Yices gives a value of an uninterpreted sort as a scalar constant as well
TEST(Yices2Datatypes, UninterpretedValueIsNoConstructor)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort u = s->make_sort("U", 0);
  Term x = s->make_symbol("x", u);
  Term y = s->make_symbol("y", u);
  s->assert_formula(s->make_term(Distinct, x, y));
  ASSERT_TRUE(s->check_sat().is_sat());
  Term x_value = s->get_value(x);

  EXPECT_THROW(s->make_term(Apply_Constructor, x_value),
               IncorrectUsageException);
  EXPECT_THROW(s->make_term(Apply_Tester, x_value, y), IncorrectUsageException);
}

TEST(Yices2Datatypes, TesterIsAnEquality)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  Sort color = declare_enum(s, "Color", { "red", "green" });
  Term red = s->make_term(Apply_Constructor, s->get_constructor(color, "red"));
  Term x = s->make_symbol("x", color);
  EXPECT_EQ(s->make_term(Apply_Tester, s->get_tester(color, "red"), x),
            s->make_term(Equal, x, red));
}

// Yices keeps type and term names in one table for the whole process
TEST(Yices2Datatypes, TwoSolversDeclareTheSameDatatype)
{
  SmtSolver s1 = Yices2SolverFactory::create(false);
  SmtSolver s2 = Yices2SolverFactory::create(false);
  Sort color1 = declare_enum(s1, "Color", { "red", "green" });
  Sort color2 = declare_enum(s2, "Color", { "green", "red" });
  EXPECT_NE(color1, color2);

  const std::vector<std::pair<SmtSolver, Sort>> declared{ { s1, color1 },
                                                          { s2, color2 } };
  for (const auto & [s, color] : declared)
  {
    Term red = s->get_constructor(color, "red");
    EXPECT_EQ(red->get_sort(), color);
    EXPECT_EQ(red->to_string(), "red");
    Term x = s->make_symbol("x", color);
    s->assert_formula(s->make_term(Distinct, x, red));
    ASSERT_TRUE(s->check_sat().is_sat());
    EXPECT_EQ(s->get_value(x), s->get_constructor(color, "green"));
  }
}

TEST(Yices2Datatypes, ArrayModelOverAnEnumeration)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort color = declare_enum(s, "Color", { "red", "green", "blue" });
  Term red = s->get_constructor(color, "red");
  Term blue = s->get_constructor(color, "blue");
  Term a = s->make_symbol("a", s->make_sort(ARRAY, color, color));
  s->assert_formula(s->make_term(Equal, s->make_term(Select, a, red), blue));
  ASSERT_TRUE(s->check_sat().is_sat());

  Term base;
  UnorderedTermMap values = s->get_array_values(a, base);
  Term at_red = values.count(red) ? values.at(red) : base;
  EXPECT_EQ(at_red, blue);
  EXPECT_EQ(base->get_sort(), color);
}

// The model writes a value of an uninterpreted sort as a scalar too, and
// get_array_values has to give the term get_value gives for it
TEST(Yices2Datatypes, ArrayModelOverAnUninterpretedSort)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  s->set_opt("produce-models", "true");
  Sort intsort = s->make_sort(INT);
  Sort u = s->make_sort("U", 0);
  Term a = s->make_symbol("a", s->make_sort(ARRAY, intsort, u));
  Term x = s->make_symbol("x", u);
  Term y = s->make_symbol("y", u);
  Term zero = s->make_term(0, intsort);
  Term one = s->make_term(1, intsort);
  s->assert_formula(s->make_term(Distinct, x, y));
  s->assert_formula(s->make_term(Equal, s->make_term(Select, a, zero), x));
  s->assert_formula(s->make_term(Equal, s->make_term(Select, a, one), y));
  ASSERT_TRUE(s->check_sat().is_sat());

  Term base;
  UnorderedTermMap values = s->get_array_values(a, base);
  Term at_zero = values.count(zero) ? values.at(zero) : base;
  Term at_one = values.count(one) ? values.at(one) : base;
  EXPECT_EQ(at_zero, s->get_value(x));
  EXPECT_EQ(at_one, s->get_value(y));
}

}  // namespace
