/*********************                                                        */
/*! \file test-generic-solver.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/

#include <gtest/gtest.h>

#include <chrono>
#include <functional>
#include <map>
#include <memory>
#include <ostream>
#include <string>
#include <tuple>
#include <vector>

#include "generic_solver.h"
#include "generic_term.h"
#include "smt.h"
#include "utils.h"

using namespace smt;
using namespace std;

namespace smt_tests {

// No command below asks a solver to do any real work, and none has been
// measured taking as much as a tenth of a second even once, so a solver
// silent for this long has stopped answering. The library default is a
// deadlock backstop sized for genuine solving; a bound this much tighter
// costs nothing here and keeps a wedged run from occupying a CI job.
const std::chrono::seconds solver_response_timeout(2);

enum class GenericBinary
{
  Cvc5,
  Msat,
  Yices2,
  Btor,
  Bitwuzla,
  Z3
};

// The binaries whose executable configure found, and where. It looks only
// for the solvers being built: under the solver's root first, which is where
// a provisioned copy lives, then on the PATH, which is where a system one
// does. A built solver without an executable is left out of every suite.
const map<GenericBinary, string> binary_paths = {
#ifdef CVC5_BINARY
  { GenericBinary::Cvc5, CVC5_BINARY },
#endif
#ifdef MATHSAT_BINARY
  { GenericBinary::Msat, MATHSAT_BINARY },
#endif
#ifdef YICES2_BINARY
  { GenericBinary::Yices2, YICES2_BINARY },
#endif
#ifdef BOOLECTOR_BINARY
  { GenericBinary::Btor, BOOLECTOR_BINARY },
#endif
#ifdef BITWUZLA_BINARY
  { GenericBinary::Bitwuzla, BITWUZLA_BINARY },
#endif
#ifdef Z3_BINARY
  { GenericBinary::Z3, Z3_BINARY },
#endif
};

void init_solver(SmtSolver gs)
{
  gs->set_opt("produce-models", "true");
  gs->set_opt("produce-unsat-assumptions", "true");
  gs->set_logic("ALL");
}

void new_btor(SmtSolver & gs, int buffer_size)
{
  gs.reset();
  string path = binary_paths.at(GenericBinary::Btor);
  vector<string> args = { "--incremental" };
  gs = std::make_shared<GenericSolver>(
      path, args, solver_response_timeout, buffer_size);
  init_solver(gs);
}

void new_bitwuzla(SmtSolver & gs, int buffer_size)
{
  gs.reset();
  string path = binary_paths.at(GenericBinary::Bitwuzla);
  // Bitwuzla is always incremental, so it has no flag for it
  vector<string> args = { "--lang", "smt2" };
  gs = std::make_shared<GenericSolver>(
      path, args, solver_response_timeout, buffer_size);
  init_solver(gs);
}

void new_msat(SmtSolver & gs, int buffer_size)
{
  gs.reset();
  string path = binary_paths.at(GenericBinary::Msat);
  vector<string> args = { "" };
  gs = std::make_shared<GenericSolver>(
      path, args, solver_response_timeout, buffer_size);
  init_solver(gs);
}

void new_yices2(SmtSolver & gs, int buffer_size)
{
  gs.reset();
  string path = binary_paths.at(GenericBinary::Yices2);
  vector<string> args = { "--incremental" };
  gs = std::make_shared<GenericSolver>(
      path, args, solver_response_timeout, buffer_size);
  init_solver(gs);
}

void new_cvc5(SmtSolver & gs, int buffer_size)
{
  gs.reset();
  string path = binary_paths.at(GenericBinary::Cvc5);
  vector<string> args = {
    "--lang=smt2", "--incremental", "--dag-thresh=0", "--arrays-exp"
  };
  gs = std::make_shared<GenericSolver>(
      path, args, solver_response_timeout, buffer_size);
  init_solver(gs);
}

void new_z3(SmtSolver & gs, int buffer_size)
{
  gs.reset();
  string path = binary_paths.at(GenericBinary::Z3);
  // Z3 reads SMT-LIB 2 from standard input only when told to, and is
  // incremental without a flag
  vector<string> args = { "-smt2", "-in" };
  gs = std::make_shared<GenericSolver>(
      path, args, solver_response_timeout, buffer_size);
  init_solver(gs);
}

string binary_name(GenericBinary b)
{
  switch (b)
  {
    case GenericBinary::Cvc5: return "Cvc5";
    case GenericBinary::Msat: return "Msat";
    case GenericBinary::Yices2: return "Yices2";
    case GenericBinary::Btor: return "Btor";
    case GenericBinary::Bitwuzla: return "Bitwuzla";
    case GenericBinary::Z3: return "Z3";
  }
  return "Unknown";
}

ostream & operator<<(ostream & o, GenericBinary b)
{
  return o << binary_name(b);
}

/** The native backend built on the same solver, whose attributes describe
 *  what the binary accepts unless has_attribute says otherwise.
 */
SolverEnum native_backend(GenericBinary b)
{
  switch (b)
  {
    case GenericBinary::Cvc5: return CVC5;
    case GenericBinary::Msat: return MSAT;
    case GenericBinary::Yices2: return YICES2;
    case GenericBinary::Btor: return BTOR;
    case GenericBinary::Bitwuzla: return BZLA;
    case GenericBinary::Z3: return Z3;
  }
  throw NotImplementedException("Unhandled generic binary");
}

/** Whether the binary accepts what the attribute describes: its native
 *  backend's attribute, except where the binary was seen to differ.
 */
bool has_attribute(GenericBinary b, SolverAttribute a)
{
  // The mathsat binary answers every check-sat over a quantified assertion
  // with (error "The CNF conversion does not support quantifiers"), though
  // the backend built on its API claims quantifiers.
  if (b == GenericBinary::Msat && a == QUANTIFIERS)
  {
    return false;
  }
  // The bitwuzla binary accepts declare-sort, which is all these tests
  // ask of it: they declare a sort and never solve over it. The native
  // backend declares them too but cannot reason about them, which is why
  // BZLA does not claim the attribute -- see src/solver_enums.cpp.
  if (b == GenericBinary::Bitwuzla && a == UNINTERP_SORT)
  {
    return true;
  }
  // With produce-unsat-assumptions on, as init_solver sets it for every
  // binary, Bitwuzla 0.9.1 answers unknown to an equality with a constant
  // array, warning "Equality over constant arrays not fully supported yet".
  // Without that option it answers sat.
  if (b == GenericBinary::Bitwuzla && a == CONSTARR)
  {
    return false;
  }
  return solver_has_attribute(native_backend(b), a);
}

/** Whether the binary accepts a function returning an array, which no
 *  SolverAttribute covers. Boolector does not: "only bit-vector sorts
 *  supported as return sort for arity > 0".
 */
bool has_array_returning_functions(GenericBinary b)
{
  return b != GenericBinary::Btor;
}

/** Whether the binary refuses a set-option it does not know, as SMT-LIB
 *  requires, which is what reaches the caller as an error. No
 *  SolverAttribute covers it. Bitwuzla 0.9.1 answers success instead.
 */
bool rejects_unknown_options(GenericBinary b)
{
  return b != GenericBinary::Bitwuzla;
}

// We test a representative set of buffer sizes, including the smallest and
// biggest supported, and a mixture of powers of two and non-powers of two.
const vector<int> buffer_sizes = { 2, 10, 64, 100, 256 };

// (solver binary, buffer size)
typedef tuple<GenericBinary, int> GenericSolverParam;

/** Every buffer size for each available binary that passes the filter */
vector<GenericSolverParam> params_where(
    const function<bool(GenericBinary)> & filter)
{
  vector<GenericSolverParam> params;
  for (const auto & entry : binary_paths)
  {
    GenericBinary b = entry.first;
    if (!filter(b))
    {
      continue;
    }
    for (int size : buffer_sizes)
    {
      params.emplace_back(b, size);
    }
  }
  return params;
}

vector<GenericSolverParam> params_with(SolverAttribute a)
{
  return params_where([a](GenericBinary b) { return has_attribute(b, a); });
}

string param_name(const testing::TestParamInfo<GenericSolverParam> & info)
{
  return binary_name(get<0>(info.param)) + "_Buf"
         + std::to_string(get<1>(info.param));
}

// The suites below share this fixture and differ only in what the binaries
// they are instantiated with must support. A build without such a binary
// leaves a suite uninstantiated.
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(GenericSolverTests);
class GenericSolverTests : public ::testing::TestWithParam<GenericSolverParam>
{
 protected:
  void SetUp() override
  {
    binary = get<0>(GetParam());
    int buffer_size = get<1>(GetParam());
    switch (binary)
    {
      case GenericBinary::Cvc5: new_cvc5(gs, buffer_size); break;
      case GenericBinary::Msat: new_msat(gs, buffer_size); break;
      case GenericBinary::Yices2: new_yices2(gs, buffer_size); break;
      case GenericBinary::Btor: new_btor(gs, buffer_size); break;
      case GenericBinary::Bitwuzla: new_bitwuzla(gs, buffer_size); break;
      case GenericBinary::Z3: new_z3(gs, buffer_size); break;
    }
  }

  GenericBinary binary;
  SmtSolver gs;
};

// binaries refusing an unknown option
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(GenericSolverOptionTests);
class GenericSolverOptionTests : public GenericSolverTests
{
};

// binaries accepting declare-sort
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(GenericSolverUfTests);
class GenericSolverUfTests : public GenericSolverTests
{
};

// binaries with integers
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(GenericSolverIntTests);
class GenericSolverIntTests : public GenericSolverTests
{
};

// binaries accepting a function that returns an array
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(GenericSolverArrayFunTests);
class GenericSolverArrayFunTests : public GenericSolverTests
{
};

// binaries with integers and quantifiers
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(GenericSolverIntQuantifierTests);
class GenericSolverIntQuantifierTests : public GenericSolverTests
{
};

// binaries with constant arrays
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(GenericSolverConstArrayTests);
class GenericSolverConstArrayTests : public GenericSolverTests
{
};

TEST_P(GenericSolverOptionTests, BadCmd)
{
  EXPECT_THROW(gs->set_opt("iiiaaaaiiiiaaaa", "aaa"), IncorrectUsageException);
}

TEST_P(GenericSolverUfTests, Uf1)
{
  Sort s = gs->make_sort("S", 0);
  EXPECT_EQ(s->get_sort_kind(), UNINTERPRETED);
  EXPECT_THROW(gs->make_sort("S", 1), IncorrectUsageException);
}

TEST_P(GenericSolverTests, Bool1)
{
  Sort bool_sort = gs->make_sort(BOOL);
  Term term_1 = gs->make_symbol("term_1", bool_sort);
  Result r;
  gs->push(1);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_sat());
  gs->pop(1);

  gs->push(1);
  gs->assert_formula(term_1);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_sat());
  gs->pop(1);
}

TEST_P(GenericSolverTests, Bool2)
{
  Term true_term_1 = gs->make_term(true);
  Term false_term_1 = gs->make_term(false);

  Term true_term_2 = gs->make_term(true);
  Term false_term_2 = gs->make_term(false);
  EXPECT_EQ(true_term_1.get(), true_term_2.get());
  EXPECT_EQ(false_term_1.get(), false_term_2.get());

  Term true_term = true_term_1;
  Term false_term = false_term_1;

  Result r;

  gs->push(1);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_sat());
  gs->pop(1);

  gs->push(1);
  gs->assert_formula(true_term);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_sat());
  gs->pop(1);

  gs->push(1);
  gs->assert_formula(false_term);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_unsat());
  gs->pop(1);

  gs->push(1);
  gs->assert_formula(false_term);
  gs->assert_formula(true_term);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_unsat());
  gs->pop(1);
}

TEST_P(GenericSolverIntTests, Int1)
{
  Sort int_sort = gs->make_sort(INT);

  Sort int_sort2 = gs->make_sort(INT);
  EXPECT_EQ(int_sort, int_sort2);

  EXPECT_THROW(gs->make_sort(ARRAY), IncorrectUsageException);
}

TEST_P(GenericSolverTests, Bv1)
{
  Sort bv_sort = gs->make_sort(BV, 4);

  Sort bv_sort1 = gs->make_sort(BV, 4);
  EXPECT_EQ(bv_sort, bv_sort1);
  Sort bv_sort2 = gs->make_sort(BV, 5);
  EXPECT_NE(bv_sort, bv_sort2);

  EXPECT_THROW(gs->make_sort(INT, bv_sort), IncorrectUsageException);
}

TEST_P(GenericSolverTests, Bv2)
{
  EXPECT_THROW(gs->make_sort(INT, 4), IncorrectUsageException);
}

TEST_P(GenericSolverUfTests, Uf2)
{
  Sort s = gs->make_sort("S", 0);
  Term svar1 = gs->make_symbol("x_s1", s);
  EXPECT_EQ(svar1->get_sort(), s);
  EXPECT_THROW(gs->make_symbol("x_s1", s), IncorrectUsageException);
}

TEST_P(GenericSolverIntTests, Int2)
{
  Sort int_sort = gs->make_sort(INT);
  Term int_zero = gs->make_term(0, int_sort);
  Term int_one = gs->make_term(1, int_sort);

  Term int_one_equal_zero =
      gs->make_term(Equal, TermVec({ int_one, int_zero }));

  gs->push(1);
  gs->assert_formula(int_one_equal_zero);
  Result r;
  r = gs->check_sat();
  EXPECT_TRUE(r.is_unsat());
  gs->pop(1);

  gs->push(1);
  Term int_one_equal_one = gs->make_term(Equal, TermVec({ int_one, int_one }));
  gs->assert_formula(int_one_equal_one);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_sat());
  gs->pop(1);
}

TEST_P(GenericSolverIntTests, BadTermEqual)
{
  Sort int_sort = gs->make_sort(INT);
  Term int_one = gs->make_term(1, int_sort);

  Sort bv_sort = gs->make_sort(BV, 4);
  Term bv_one = gs->make_term(1, bv_sort);
  EXPECT_THROW(gs->make_term(Equal, TermVec({ bv_one, int_one })),
               IncorrectUsageException);
}

TEST_P(GenericSolverIntTests, BadTermBVAdd)
{
  Sort int_sort = gs->make_sort(INT);
  Term int_one = gs->make_term(1, int_sort);

  Sort bv_sort = gs->make_sort(BV, 4);
  Term bv_one = gs->make_term(1, bv_sort);
  EXPECT_THROW(gs->make_term(BVAdd, TermVec({ bv_one, int_one })),
               IncorrectUsageException);
}

TEST_P(GenericSolverTests, Bv3)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term bv_zero = gs->make_term(0, bv_sort);
  Term bv_one = gs->make_term(1, bv_sort);
  Term bv_minus_one_int = gs->make_term(-1, bv_sort);
  Term bv_minus_one_dec = gs->make_term("-1", bv_sort);
  Term bv_minus_one_bin = gs->make_term("1111", bv_sort, 2);
  Term bv_minus_one_hex = gs->make_term("F", bv_sort, 16);
  EXPECT_EQ(bv_minus_one_int, bv_minus_one_dec);
  EXPECT_NE(bv_minus_one_int, bv_minus_one_bin);
  EXPECT_NE(bv_minus_one_int, bv_minus_one_hex);
  EXPECT_NE(bv_minus_one_bin, bv_minus_one_hex);
  gs->push(1);
  Term eq1 = gs->make_term(Equal, bv_minus_one_dec, bv_minus_one_bin);
  Term eq2 = gs->make_term(Equal, bv_minus_one_int, bv_minus_one_bin);
  Term eq3 = gs->make_term(Equal, bv_minus_one_int, bv_minus_one_dec);
  Term eq4 = gs->make_term(Equal, bv_minus_one_int, bv_minus_one_hex);
  gs->assert_formula(eq1);
  gs->assert_formula(eq2);
  gs->assert_formula(eq3);
  gs->assert_formula(eq4);
  Result r;
  r = gs->check_sat();
  EXPECT_TRUE(r.is_sat());
  gs->pop(1);

  Term bv_one_equal_zero = gs->make_term(Equal, TermVec({ bv_one, bv_zero }));
  gs->push(1);
  gs->assert_formula(bv_one_equal_zero);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_unsat());
  gs->pop(1);

  gs->push(1);
  Term bv_one_equal_one = gs->make_term(Equal, bv_one, bv_one);
  gs->assert_formula(bv_one_equal_one);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_sat());
  gs->pop(1);
}

TEST_P(GenericSolverTests, Bv4)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term bv_zero = gs->make_term(0, bv_sort);
  Term bv_one = gs->make_term(1, bv_sort);
  Term bv_one_equal_zero = gs->make_term(Equal, TermVec({ bv_one, bv_zero }));
  gs->push(1);
  gs->assert_formula(bv_one_equal_zero);
  Result r;
  r = gs->check_sat();
  EXPECT_TRUE(r.is_unsat());
  gs->pop(1);

  gs->push(1);
  Term bv_one_equal_one = gs->make_term(Equal, bv_one, bv_one);
  gs->assert_formula(bv_one_equal_one);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_sat());
  gs->pop(1);
}

TEST_P(GenericSolverTests, Abv1)
{
  Sort bv_sort1 = gs->make_sort(BV, 4);
  Sort bv_sort2 = gs->make_sort(BV, 5);

  Sort bv_to_bv = gs->make_sort(ARRAY, bv_sort1, bv_sort2);
  Term arr_var = gs->make_symbol("a", bv_to_bv);
  EXPECT_EQ(arr_var->get_sort(), bv_to_bv);
  Sort bv_x_bv_to_array = gs->make_sort(FUNCTION, bv_sort1, bv_sort2, bv_to_bv);
  EXPECT_EQ(bv_x_bv_to_array->get_sort_kind(), FUNCTION);
}

TEST_P(GenericSolverTests, Bool)
{
  Term true_term_1 = gs->make_term(true);
  Term false_term_1 = gs->make_term(false);

  Term true_term_2 = gs->make_term(true);
  Term false_term_2 = gs->make_term(false);
  EXPECT_EQ(true_term_1.get(), true_term_2.get());
  EXPECT_EQ(false_term_1.get(), false_term_2.get());

  Term true_term = true_term_1;
  Term false_term = false_term_1;

  Result r;

  gs->push(1);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_sat());
  gs->pop(1);
  gs->push(1);
  gs->assert_formula(true_term);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_sat());
  gs->pop(1);

  gs->push(1);
  gs->assert_formula(false_term);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_unsat());
  gs->pop(1);

  gs->push(1);
  gs->assert_formula(false_term);
  gs->assert_formula(true_term);
  r = gs->check_sat();
  EXPECT_TRUE(r.is_unsat());
  gs->pop(1);
}

TEST_P(GenericSolverArrayFunTests, Abv2)
{
  gs->push(1);
  Sort bv_sort1 = gs->make_sort(BV, 4);
  Sort bv_sort2 = gs->make_sort(BV, 5);
  Sort bv_to_bv = gs->make_sort(ARRAY, bv_sort1, bv_sort2);
  Sort bv_x_bv_to_array = gs->make_sort(FUNCTION, bv_sort1, bv_sort2, bv_to_bv);

  Term complex1 = gs->make_symbol("complex1", bv_x_bv_to_array);
  Sort bv_sort = gs->make_sort(BV, 4);
  Term bv_zero = gs->make_term(0, bv_sort);
  Term bv_one = gs->make_term(1, bv_sort);

  Term arr1 = gs->make_term(
      Apply,
      TermVec{ complex1,
               bv_zero,
               gs->make_term(
                   Concat, bv_one, gs->make_term("0", gs->make_sort(BV, 1))) });
  Term sel1 = gs->make_term(Select, arr1, bv_one);
  Term dis1 =
      gs->make_term(Distinct, sel1, gs->make_term("1", gs->make_sort(BV, 5)));

  gs->push(1);
  Term bv1 = gs->make_symbol("bv", bv_sort);
  Term for1 = gs->make_term(Equal, bv1, bv_zero);
  gs->assert_formula(for1);
  gs->assert_formula(dis1);
  Result result = gs->check_sat();
  ASSERT_TRUE(result.is_sat());
  EXPECT_EQ(gs->get_value(bv1)->to_int(), 0u);
  EXPECT_EQ(gs->get_value(dis1), gs->make_term(true));
  gs->pop(1);
}

TEST_P(GenericSolverIntQuantifierTests, Quantifiers)
{
  gs->push(1);
  Sort int_sort = gs->make_sort(INT);
  Term par1 = gs->make_param("par1", int_sort);
  Term par2 = gs->make_param("par2", int_sort);
  Term sum = gs->make_term(Plus, par1, par2);
  Term matrix1 = gs->make_term(Gt, par1, sum);
  Term exists1 = gs->make_term(Exists, par2, matrix1);
  Term forall1 = gs->make_term(Forall, par1, exists1);
  gs->assert_formula(forall1);
  Result result = gs->check_sat();
  EXPECT_TRUE(result.is_sat());
  Term matrix2 = gs->make_term(Gt, par1, par2);
  Term forall2 = gs->make_term(Forall, par1, matrix2);
  Term exists2 = gs->make_term(Exists, par2, forall2);
  gs->assert_formula(exists2);
  result = gs->check_sat();
  EXPECT_TRUE(result.is_unsat());
  gs->pop(1);
}

TEST_P(GenericSolverConstArrayTests, ConstantArrays)
{
  // Testing constant arrays
  gs->push(1);
  Sort bvsort = gs->make_sort(BV, 4);
  Sort arrsort = gs->make_sort(ARRAY, bvsort, bvsort);
  Term zero = gs->make_term(0, bvsort);
  Term constarr0 = gs->make_term(zero, arrsort);
  Term arr = gs->make_symbol("arr", arrsort);
  Term arreq = gs->make_term(Equal, arr, constarr0);
  gs->assert_formula(arreq);
  Result result = gs->check_sat();
  EXPECT_TRUE(result.is_sat());
  gs->pop(1);
}

TEST_P(GenericSolverIntTests, IntModels)
{
  // Testing models
  gs->push(1);
  Sort int_sort = gs->make_sort(INT);
  Term int_zero = gs->make_term(0, int_sort);
  Term i1 = gs->make_symbol("i", int_sort);
  Term for1 = gs->make_term(Equal, i1, int_zero);
  gs->assert_formula(for1);
  Result result = gs->check_sat();
  ASSERT_TRUE(result.is_sat());
  EXPECT_EQ(gs->get_value(i1), int_zero);
  EXPECT_EQ(gs->get_value(for1), gs->make_term(true));
  gs->pop(1);
}

TEST_P(GenericSolverIntTests, NegativeIntModels)
{
  gs->push(1);
  Sort int_sort = gs->make_sort(INT);
  Term minus_five = gs->make_term(-5, int_sort);
  // SMT-LIB has no negative numerals, so -5 would be a symbol, though
  // cvc5 accepts it
  EXPECT_EQ(minus_five->to_string(), "(- 5)");
  Term i1 = gs->make_symbol("i", int_sort);
  gs->assert_formula(gs->make_term(Equal, i1, minus_five));
  Result result = gs->check_sat();
  ASSERT_TRUE(result.is_sat());
  EXPECT_EQ(gs->get_value(i1)->to_string(), minus_five->to_string());
  gs->pop(1);
}

TEST_P(GenericSolverTests, BvModels)
{
  // Testing models
  gs->push(1);
  Sort bv_sort = gs->make_sort(BV, 4);
  Term bv_zero = gs->make_term(0, bv_sort);
  Term i1 = gs->make_symbol("i", bv_sort);
  Term for1 = gs->make_term(Equal, i1, bv_zero);
  gs->assert_formula(for1);
  Result result = gs->check_sat();
  ASSERT_TRUE(result.is_sat());
  EXPECT_EQ(gs->get_value(i1)->to_int(), 0u);
  // MathSAT answers in the (_ bv0 4) notation make_term uses, so there
  // the value read back must be the same term
  if (binary == GenericBinary::Msat)
  {
    EXPECT_EQ(gs->get_value(i1)->to_string(), bv_zero->to_string());
  }
  gs->pop(1);
}

TEST_P(GenericSolverTests, NonNumericSortValue)
{
  Sort bool_sort = gs->make_sort(BOOL);
  EXPECT_THROW(gs->make_term(1, bool_sort), IncorrectUsageException);
  EXPECT_THROW(gs->make_term("1", bool_sort), IncorrectUsageException);
}

TEST_P(GenericSolverTests, GetValueUnsupportedSort)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term arr = gs->make_symbol("arr", gs->make_sort(ARRAY, bv_sort, bv_sort));
  Term f = gs->make_symbol("f", gs->make_sort(FUNCTION, bv_sort, bv_sort));
  ASSERT_TRUE(gs->check_sat().is_sat());
  EXPECT_THROW(gs->get_value(arr), NotImplementedException);
  EXPECT_THROW(gs->get_value(f), NotImplementedException);
}

TEST_P(GenericSolverTests, GetValueForeignTerm)
{
  // a symbol made outside this solver, which never declared it
  Term foreign = std::make_shared<GenericTerm>(
      gs->make_sort(BV, 4), Op(), TermVec{}, "|foreign|", true);
  ASSERT_TRUE(gs->check_sat().is_sat());
  EXPECT_THROW(gs->get_value(foreign), IncorrectUsageException);
}

TEST_P(GenericSolverTests, CheckSatAssuming1)
{
  // Testing check-sat-assuming
  gs->push(1);
  Sort bool_sort = gs->make_sort(BOOL);
  Term b1 = gs->make_symbol("bool1", bool_sort);
  Term not_b1 = gs->make_term(Not, b1);
  Term b2 = gs->make_symbol("bool2", bool_sort);
  Term b3 = gs->make_symbol("bool3", bool_sort);
  gs->assert_formula(b1);
  Result r;
  r = gs->check_sat_assuming(TermVec{ not_b1, b2, b3 });
  EXPECT_TRUE(r.is_unsat());
  gs->pop(1);
}

TEST_P(GenericSolverTests, CheckSatAssuming2)
{
  // Testing check-sat-assuming
  gs->push(1);
  Sort bv_sort = gs->make_sort(BV, 4);
  Term bv1 = gs->make_symbol("bv1", bv_sort);
  Term bv2 = gs->make_symbol("bv2", bv_sort);

  Term b1 = gs->make_term(Equal, bv1, gs->make_term(BVNot, bv2));
  gs->make_term(Not, b1);

  Term b2 = gs->make_term(BVUgt, bv1, bv2);

  Term b3 = gs->make_term(BVUgt, bv2, gs->make_term(3, bv_sort));
  gs->assert_formula(b1);
  Result r;
  r = gs->check_sat_assuming(TermVec{ b2, b3 });
  EXPECT_TRUE(r.is_sat());
  gs->pop(1);
}

TEST_P(GenericSolverTests, UnsatAssumptions)
{
  // Testing unsat-assumptions
  gs->push(1);
  Sort bool_sort = gs->make_sort(BOOL);
  Term b1 = gs->make_symbol("bool11", bool_sort);
  Term not_b1 = gs->make_term(Not, b1);
  Term b2 = gs->make_symbol("bool22", bool_sort);
  Term b3 = gs->make_symbol("bool33", bool_sort);
  gs->assert_formula(b1);
  Result r = gs->check_sat_assuming(TermVec{ not_b1, b2, b3 });
  ASSERT_TRUE(r.is_unsat());
  UnorderedTermSet core;
  gs->get_unsat_assumptions(core);
  // b1 is asserted and b2, b3 are free, so any core needs (not b1).
  // Boolector itself answers wrongly, not the parsing here: assuming a
  // name defined as (not bool11), get-unsat-assumptions gives (bool11),
  // and assuming the literal (not bool11) it gives (false).
  Term culprit = binary == GenericBinary::Btor ? b1 : not_b1;
  EXPECT_NE(core.find(culprit), core.end());
  gs->pop(1);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedGenericSolverTests,
                         GenericSolverTests,
                         testing::ValuesIn(params_where([](GenericBinary) {
                           return true;
                         })),
                         param_name);

INSTANTIATE_TEST_SUITE_P(
    ParameterizedGenericSolverOptionTests,
    GenericSolverOptionTests,
    testing::ValuesIn(params_where(rejects_unknown_options)),
    param_name);

INSTANTIATE_TEST_SUITE_P(ParameterizedGenericSolverUfTests,
                         GenericSolverUfTests,
                         testing::ValuesIn(params_with(UNINTERP_SORT)),
                         param_name);

INSTANTIATE_TEST_SUITE_P(ParameterizedGenericSolverIntTests,
                         GenericSolverIntTests,
                         testing::ValuesIn(params_with(THEORY_INT)),
                         param_name);

INSTANTIATE_TEST_SUITE_P(
    ParameterizedGenericSolverArrayFunTests,
    GenericSolverArrayFunTests,
    testing::ValuesIn(params_where(has_array_returning_functions)),
    param_name);

INSTANTIATE_TEST_SUITE_P(ParameterizedGenericSolverIntQuantifierTests,
                         GenericSolverIntQuantifierTests,
                         testing::ValuesIn(params_where([](GenericBinary b) {
                           return has_attribute(b, THEORY_INT)
                                  && has_attribute(b, QUANTIFIERS);
                         })),
                         param_name);

INSTANTIATE_TEST_SUITE_P(ParameterizedGenericSolverConstArrayTests,
                         GenericSolverConstArrayTests,
                         testing::ValuesIn(params_with(CONSTARR)),
                         param_name);

TEST(GenericSolver, NonExistingBinary)
{
  EXPECT_THROW(
      std::make_shared<GenericSolver>(
          "/non/existing/path", vector<string>{}, solver_response_timeout, 5),
      IncorrectUsageException);
}

TEST(GenericSolver, BinaryClosedItsInput)
{
  // the binary closes its input before answering the first command, so
  // the constructor's next command at the latest goes to a pipe nobody
  // reads
  EXPECT_THROW(
      std::make_shared<GenericSolver>(
          "/bin/sh",
          vector<string>{ "-c", "exec 0<&-; echo success; exec sleep 10" },
          solver_response_timeout,
          5),
      InternalSolverException);
}

}  // namespace smt_tests
