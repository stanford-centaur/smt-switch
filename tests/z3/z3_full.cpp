#include <gtest/gtest.h>

#include "smt.h"
#include "z3_factory.h"

using namespace smt;

TEST(Z3Full, IntegerConstraintsAndBVValues)
{
  SmtSolver s = Z3SolverFactory::create(false);

  Sort intsort = s->make_sort(INT);
  EXPECT_EQ(intsort->get_sort_kind(), INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term val1 = s->make_term(1, intsort);
  Term val3 = s->make_term(3, intsort);
  EXPECT_TRUE(x->is_symbolic_const());
  EXPECT_EQ(x->get_sort(), intsort);
  EXPECT_NE(x, y);
  EXPECT_TRUE(val1->is_value());
  EXPECT_EQ(val1->to_int(), 1);
  EXPECT_EQ(val3->to_int(), 3);

  Term xge = s->make_term(Op(Ge), x, val1);
  Term xplus = s->make_term(Op(Plus), x, val3);
  Term ylt = s->make_term(Op(Lt), y, xplus);
  EXPECT_EQ(xge->get_op(), Op(Ge));
  EXPECT_EQ(xplus->get_op(), Op(Plus));
  EXPECT_EQ(ylt->get_op(), Op(Lt));
  EXPECT_EQ(xge->get_sort()->get_sort_kind(), BOOL);
  EXPECT_EQ(xplus->get_sort(), intsort);

  s->assert_formula(xge);
  s->assert_formula(ylt);

  Result r = s->check_sat();
  EXPECT_TRUE(r.is_sat());

  Term xlt = s->make_term(Op(Lt), x, val1);
  s->assert_formula(xlt);
  r = s->check_sat();
  EXPECT_TRUE(r.is_unsat());

  Sort bvsort = s->make_sort(BV, 7);
  EXPECT_EQ(bvsort->get_sort_kind(), BV);
  EXPECT_EQ(bvsort->get_width(), 7);
  Term bin = s->make_term("0000010", bvsort, 2);
  Term hex = s->make_term("0F", bvsort, 16);
  EXPECT_EQ(bin->to_int(), 2);
  EXPECT_EQ(hex->to_int(), 15);
  EXPECT_EQ(bin->get_sort(), bvsort);
}
