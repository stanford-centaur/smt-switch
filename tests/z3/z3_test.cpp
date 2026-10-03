#include <gtest/gtest.h>

#include "datatype.h"
#include "smt.h"
#include "z3_factory.h"
#include "z3_sort.h"

using namespace smt;

TEST(Z3Test, SortsAndTerms)
{
  SmtSolver s = Z3SolverFactory::create(false);

  Sort boolsort1 = s->make_sort(BOOL);
  Sort realsort1 = s->make_sort(REAL);
  Sort intsort1 = s->make_sort(INT);
  EXPECT_EQ(boolsort1->get_sort_kind(), BOOL);
  EXPECT_EQ(realsort1->get_sort_kind(), REAL);
  EXPECT_EQ(intsort1->get_sort_kind(), INT);

  Sort bvsort = s->make_sort(BV, 8);
  EXPECT_EQ(bvsort->get_sort_kind(), BV);
  EXPECT_EQ(bvsort->get_width(), 8);

  Sort uninterpretedsort = s->make_sort("a test", 0);
  EXPECT_EQ(uninterpretedsort->get_sort_kind(), UNINTERPRETED);
  EXPECT_EQ(uninterpretedsort->get_uninterpreted_name(), "a test");

  Sort arraysort = s->make_sort(ARRAY, intsort1, bvsort);
  EXPECT_EQ(arraysort->get_sort_kind(), ARRAY);
  EXPECT_EQ(arraysort->get_indexsort(), intsort1);
  EXPECT_EQ(arraysort->get_elemsort(), bvsort);

  Sort functionsort = s->make_sort(
      FUNCTION, SortVec{ boolsort1, intsort1, realsort1, boolsort1 });
  EXPECT_EQ(functionsort->get_sort_kind(), FUNCTION);
  EXPECT_EQ(functionsort->get_domain_sorts(),
            (SortVec{ boolsort1, intsort1, realsort1 }));
  EXPECT_EQ(functionsort->get_codomain_sort(), boolsort1);

  DatatypeDecl listSpec = s->make_datatype_decl("list");
  DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
  DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");
  s->add_selector(consdecl, "head", s->make_sort(INT));
  s->add_selector_self(consdecl, "tail");
  s->add_constructor(listSpec, nildecl);
  s->add_constructor(listSpec, consdecl);
  Sort listsort = s->make_sort(listSpec);
  EXPECT_EQ(listsort->get_sort_kind(), DATATYPE);
  Datatype listdt = listsort->get_datatype();
  EXPECT_EQ(listdt->get_name(), "list");
  EXPECT_EQ(listdt->get_num_constructors(), 2);
  EXPECT_EQ(listdt->get_num_selectors("nil"), 0);
  EXPECT_EQ(listdt->get_num_selectors("cons"), 2);
  EXPECT_TRUE(
      std::static_pointer_cast<Z3Sort>(listsort)->get_z3_type().is_datatype());

  Term boolterm1 = s->make_term(true);
  Term boolterm2 = s->make_term(false);
  EXPECT_TRUE(boolterm1->is_value());
  EXPECT_TRUE(boolterm2->is_value());
  EXPECT_NE(boolterm1, boolterm2);
  EXPECT_EQ(boolterm1->get_sort(), boolsort1);

  Term intterm = s->make_term(1, intsort1);
  Term realterm = s->make_term(2, realsort1);
  Term bvterm = s->make_term(16, bvsort);
  EXPECT_EQ(intterm->get_sort(), intsort1);
  EXPECT_EQ(realterm->get_sort(), realsort1);
  EXPECT_EQ(bvterm->get_sort(), bvsort);

  EXPECT_EQ(intterm->to_int(), 1);
  EXPECT_EQ(realterm->to_int(), 2);
  EXPECT_EQ(bvterm->to_int(), 16);

  Term notBool = s->make_term(Not, boolterm1);
  Term isInt = s->make_term(Is_Int, intterm);
  EXPECT_EQ(notBool->get_op(), Op(Not));
  EXPECT_EQ(isInt->get_op(), Op(Is_Int));
  EXPECT_EQ(isInt->get_sort(), boolsort1);

  Term impl = s->make_term(Implies, boolterm1, boolterm1);
  Term andBool = s->make_term(And, boolterm1, boolterm2);
  Term concat = s->make_term(Concat, bvterm, bvterm);
  EXPECT_EQ(impl->get_op(), Op(Implies));
  EXPECT_EQ(andBool->get_op(), Op(And));
  EXPECT_EQ(concat->get_op(), Op(Concat));
  EXPECT_EQ(concat->get_sort()->get_width(), 16);

  Sort bvsort2 = s->make_sort(BV, 8);
  EXPECT_EQ(bvsort2, bvsort);
  Term bvterm2 = s->make_symbol("bvterm2", bvsort2);
  Term aext = s->make_term(Op(Extract, 3, 0), bvterm2);
  EXPECT_EQ(aext->get_op(), Op(Extract, 3, 0));
  EXPECT_EQ(aext->get_sort()->get_width(), 4);

  Term bv2nat = s->make_term(Op(BV_To_Nat), bvterm);
  Term int2bv = s->make_term(Op(Int_To_BV, 8), intterm);
  // BV_To_Nat is a deprecated alias of UBV_To_Int
  EXPECT_EQ(bv2nat->get_op(), Op(UBV_To_Int));
  EXPECT_EQ(bv2nat->get_sort(), intsort1);
  EXPECT_EQ(int2bv->get_op(), Op(Int_To_BV, 8));
  EXPECT_EQ(int2bv->get_sort(), bvsort);

  Term ext2 = s->make_term(Op(Zero_Extend, 1), bvterm);
  EXPECT_EQ(ext2->get_op(), Op(Zero_Extend, 1));
  EXPECT_EQ(ext2->get_sort()->get_width(), 9);

  Sort functionsort2 = s->make_sort(FUNCTION, SortVec{ boolsort1, intsort1 });
  Sort functionsort3 =
      s->make_sort(FUNCTION, SortVec{ boolsort1, intsort1, boolsort1 });
  Term funfun = s->make_symbol("hellooo", functionsort);
  Term funfun2 = s->make_symbol("hellooo2", functionsort2);
  Term funfun3 = s->make_symbol("hellooo3", functionsort3);
  EXPECT_EQ(funfun->get_sort(), functionsort);
  EXPECT_EQ(funfun2->get_sort(), functionsort2);
  EXPECT_EQ(funfun3->get_sort(), functionsort3);

  Term appfun =
      s->make_term(Op(Apply), TermVec{ funfun, boolterm1, intterm, realterm });
  Term appfun2 = s->make_term(Op(Apply), funfun2, boolterm1);
  Term appfun3 = s->make_term(Op(Apply), funfun3, boolterm1, intterm);
  EXPECT_EQ(appfun->get_op(), Op(Apply));
  EXPECT_EQ(appfun->get_sort(), boolsort1);
  EXPECT_EQ(appfun2->get_op(), Op(Apply));
  EXPECT_EQ(appfun2->get_sort(), intsort1);
  EXPECT_EQ(appfun3->get_op(), Op(Apply));
  EXPECT_EQ(appfun3->get_sort(), boolsort1);

  Term x = s->make_symbol("x", boolsort1);
  Term y = s->make_symbol("y", boolsort1);
  Term impx = s->make_term(Implies, x, y);
  Term qterm = s->make_term(Forall, TermVec{ x, impx });
  Term eterm = s->make_term(Exists, TermVec{ x, impx });
  EXPECT_EQ(qterm->get_op(), Op(Forall));
  EXPECT_EQ(eterm->get_op(), Op(Exists));
  EXPECT_EQ(qterm->get_sort(), boolsort1);
}

TEST(Z3Test, BvStringOutOfRange)
{
  SmtSolver s = Z3SolverFactory::create(false);
  Sort bvsort = s->make_sort(BV, 8);

  EXPECT_EQ(s->make_term("255", bvsort, 10), s->make_term(255, bvsort));
  EXPECT_EQ(s->make_term("-128", bvsort, 10), s->make_term(-128, bvsort));
  EXPECT_EQ(s->make_term("11111111", bvsort, 2), s->make_term(255, bvsort));
  EXPECT_EQ(s->make_term("-10000000", bvsort, 2), s->make_term(-128, bvsort));
  EXPECT_EQ(s->make_term("ff", bvsort, 16), s->make_term(255, bvsort));
  EXPECT_EQ(s->make_term("-80", bvsort, 16), s->make_term(-128, bvsort));

  EXPECT_THROW(s->make_term("256", bvsort, 10), IncorrectUsageException);
  EXPECT_THROW(s->make_term("-129", bvsort, 10), IncorrectUsageException);
  EXPECT_THROW(s->make_term("100000000", bvsort, 2), IncorrectUsageException);
  EXPECT_THROW(s->make_term("-10000001", bvsort, 2), IncorrectUsageException);
  EXPECT_THROW(s->make_term("100", bvsort, 16), IncorrectUsageException);
  EXPECT_THROW(s->make_term("-81", bvsort, 16), IncorrectUsageException);
}
