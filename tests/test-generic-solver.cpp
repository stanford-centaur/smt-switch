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
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <ostream>
#include <string>
#include <tuple>
#include <utility>
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
}

void new_bitwuzla(SmtSolver & gs, int buffer_size)
{
  gs.reset();
  string path = binary_paths.at(GenericBinary::Bitwuzla);
  // Bitwuzla is always incremental, so it has no flag for it
  vector<string> args = { "--lang", "smt2" };
  gs = std::make_shared<GenericSolver>(
      path, args, solver_response_timeout, buffer_size);
}

void new_msat(SmtSolver & gs, int buffer_size)
{
  gs.reset();
  string path = binary_paths.at(GenericBinary::Msat);
  vector<string> args = { "" };
  gs = std::make_shared<GenericSolver>(
      path, args, solver_response_timeout, buffer_size);
}

void new_yices2(SmtSolver & gs, int buffer_size)
{
  gs.reset();
  string path = binary_paths.at(GenericBinary::Yices2);
  vector<string> args = { "--incremental" };
  gs = std::make_shared<GenericSolver>(
      path, args, solver_response_timeout, buffer_size);
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
  // The Yices2 API writes a constant array as a lambda, but its SMT-LIB
  // frontend has no such term: the binary answers
  // (error "undefined term: const") to ((as const (Array ...)) ...).
  if (b == GenericBinary::Yices2 && a == CONSTARR)
  {
    return false;
  }
  // The boolector binary answers get-value for a select, then dies of
  // SIGSEGV on get-value for the array itself.
  if (b == GenericBinary::Btor && a == ARRAY_MODELS)
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
 *  SolverAttribute covers it. Bitwuzla answers success instead.
 */
bool rejects_unknown_options(GenericBinary b)
{
  return b != GenericBinary::Bitwuzla;
}

/** Whether the binary takes a second set-logic, which SMT-LIB forbids.
 *  Boolector and Bitwuzla do.
 */
bool accepts_second_logic(GenericBinary b)
{
  return b == GenericBinary::Btor || b == GenericBinary::Bitwuzla;
}

/** Whether the binary takes a set-logic after a declaration made without
 *  one, which SMT-LIB forbids. cvc5 settles on ALL at the declaration, and
 *  Yices2 refuses the declaration until it has a logic, so it gets ALL.
 */
bool accepts_logic_after_declaration(GenericBinary b)
{
  return b != GenericBinary::Cvc5 && b != GenericBinary::Yices2;
}

// The smallest supported buffer splits each response into as many reads as
// possible, and the biggest takes most responses in a single read.
const vector<int> buffer_sizes = { 2, 256 };

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
    start_binary();
    init_solver(gs);
  }

  // replace gs with a fresh solver, in start mode with no options set
  void start_binary()
  {
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

// binaries with reals
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(GenericSolverRealTests);
class GenericSolverRealTests : public GenericSolverTests
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

// binaries that answer get-value for an array
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(GenericSolverArrayModelTests);
class GenericSolverArrayModelTests : public GenericSolverTests
{
};

// binaries with datatypes
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(GenericSolverDatatypeTests);
class GenericSolverDatatypeTests : public GenericSolverTests
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

TEST_P(GenericSolverTests, SymbolAfterDefinedTerm)
{
  // a term defined before the symbol is made must not take its name,
  // whatever the symbol is called
  Sort bool_sort = gs->make_sort(BOOL);
  Term x = gs->make_symbol("x", bool_sort);
  gs->make_term(Not, x);
  Term t_1 = gs->make_symbol("t_1", bool_sort);
  gs->assert_formula(t_1);
  gs->assert_formula(gs->make_term(Not, t_1));
  EXPECT_TRUE(gs->check_sat().is_unsat());
}

TEST_P(GenericSolverTests, InternalNamesRefused)
{
  Sort bool_sort = gs->make_sort(BOOL);
  std::string name = internal_name("term", 1);
  EXPECT_THROW(gs->make_symbol(name, bool_sort), IncorrectUsageException);
  EXPECT_THROW(gs->make_param(name, bool_sort), IncorrectUsageException);
  EXPECT_THROW(gs->make_datatype_constructor_decl(name),
               IncorrectUsageException);
  DatatypeDecl list = gs->make_datatype_decl("list");
  DatatypeConstructorDecl cons = gs->make_datatype_constructor_decl("cons");
  gs->add_constructor(list, cons);
  EXPECT_THROW(gs->add_selector(cons, name, bool_sort),
               IncorrectUsageException);
  EXPECT_THROW(gs->add_selector_self(cons, name), IncorrectUsageException);
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

TEST_P(GenericSolverIntTests, UsableAfterIllSortedTerm)
{
  Sort int_sort = gs->make_sort(INT);
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", int_sort);
  Term int_one = gs->make_term(1, int_sort);
  Term bv_one = gs->make_term(1, bv_sort);
  EXPECT_THROW(gs->make_term(Equal, x, bv_one), IncorrectUsageException);

  gs->assert_formula(gs->make_term(Equal, x, int_one));
  ASSERT_TRUE(gs->check_sat().is_sat());
  EXPECT_EQ(gs->get_value(x), int_one);
}

TEST_P(GenericSolverIntTests, KeepsStateAfterIllSortedTerm)
{
  Sort int_sort = gs->make_sort(INT);
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", int_sort);
  Term int_one = gs->make_term(1, int_sort);
  Term bv_one = gs->make_term(1, bv_sort);
  gs->push(1);
  gs->assert_formula(gs->make_term(Equal, x, int_one));
  EXPECT_THROW(gs->make_term(Equal, x, bv_one), IncorrectUsageException);

  gs->push(1);
  gs->assert_formula(gs->make_term(Distinct, x, int_one));
  EXPECT_TRUE(gs->check_sat().is_unsat());
  gs->pop(1);
  EXPECT_TRUE(gs->check_sat().is_sat());
  gs->pop(1);
}

TEST_P(GenericSolverIntTests, UsableAfterIllSortedHeldBackTerm)
{
  Sort int_sort = gs->make_sort(INT);
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", int_sort);
  Term int_one = gs->make_term(1, int_sort);
  Term bv_one = gs->make_term(1, bv_sort);
  ASSERT_TRUE(gs->check_sat().is_sat());
  // made in the sat mode, so both are sent only by the next assertion,
  // the good one after the bad one
  gs->make_term(Equal, x, bv_one);
  Term x_is_one = gs->make_term(Equal, x, int_one);
  EXPECT_THROW(gs->assert_formula(x_is_one), IncorrectUsageException);

  gs->assert_formula(x_is_one);
  ASSERT_TRUE(gs->check_sat().is_sat());
  EXPECT_EQ(gs->get_value(x), int_one);
}

TEST_P(GenericSolverTests, UsableAfterIllSortedBvTerm)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", bv_sort);
  Term bv_one = gs->make_term(1, bv_sort);
  EXPECT_THROW(gs->make_term(Equal, x, gs->make_term(true)),
               IncorrectUsageException);

  gs->assert_formula(gs->make_term(Equal, x, bv_one));
  ASSERT_TRUE(gs->check_sat().is_sat());
  EXPECT_EQ(gs->get_value(x), bv_one);
}

TEST_P(GenericSolverIntTests, PowNeedsConstantNonNegativeExponent)
{
  Sort int_sort = gs->make_sort(INT);
  Term x = gs->make_symbol("x", int_sort);
  Term y = gs->make_symbol("y", int_sort);
  EXPECT_THROW(gs->make_term(Pow, x, y), NotImplementedException);
  EXPECT_THROW(gs->make_term(Pow, x, gs->make_term(-1, int_sort)),
               NotImplementedException);
  EXPECT_THROW(gs->make_term(Pow, TermVec({ x })), IncorrectUsageException);
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
  EXPECT_EQ(bv_minus_one_int, bv_minus_one_bin);
  EXPECT_EQ(bv_minus_one_int, bv_minus_one_hex);
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

TEST_P(GenericSolverIntTests, TwoArgumentUf)
{
  // a domain of bare words such as Int, unlike (_ BitVec 4), runs
  // together in the declare-fun unless the sorts are separated
  Sort int_sort = gs->make_sort(INT);
  Sort bool_sort = gs->make_sort(BOOL);
  Sort int_x_int_to_bool =
      gs->make_sort(FUNCTION, SortVec{ int_sort, int_sort, bool_sort });
  Term f = gs->make_symbol("f", int_x_int_to_bool);
  Term a = gs->make_symbol("a", int_sort);
  Term b = gs->make_symbol("b", int_sort);
  gs->assert_formula(gs->make_term(Apply, TermVec{ f, a, b }));
  gs->assert_formula(
      gs->make_term(Not, gs->make_term(Apply, TermVec{ f, b, a })));
  EXPECT_TRUE(gs->check_sat().is_sat());
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

TEST_P(GenericSolverIntQuantifierTests, MultipleBinders)
{
  Sort int_sort = gs->make_sort(INT);
  Term x = gs->make_param("x", int_sort);
  Term y = gs->make_param("y", int_sort);
  Term forall_xy =
      gs->make_term(Forall, TermVec{ x, y, gs->make_term(Gt, x, y) });

  // made as forall x . forall y . x > y
  EXPECT_EQ(forall_xy->get_op(), Forall);
  TermVec children(forall_xy->begin(), forall_xy->end());
  ASSERT_EQ(children.size(), 2);
  EXPECT_EQ(children[0], x);
  EXPECT_EQ(children[1]->get_op(), Forall);

  gs->assert_formula(forall_xy);
  EXPECT_TRUE(gs->check_sat().is_unsat());
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

TEST_P(GenericSolverArrayModelTests, ArrayModels)
{
  gs->push(1);
  Sort idxsort = gs->make_sort(BV, 4);
  Sort elemsort = gs->make_sort(BV, 8);
  Sort arrsort = gs->make_sort(ARRAY, idxsort, elemsort);
  Term arr = gs->make_symbol("arr", arrsort);
  Term one = gs->make_term(1, idxsort);
  Term two = gs->make_term(2, idxsort);
  Term eleven = gs->make_term(11, elemsort);
  Term twelve = gs->make_term(12, elemsort);
  gs->assert_formula(
      gs->make_term(Equal, gs->make_term(Select, arr, one), eleven));
  gs->assert_formula(
      gs->make_term(Equal, gs->make_term(Select, arr, two), twelve));
  ASSERT_TRUE(gs->check_sat().is_sat());

  Term const_base;
  UnorderedTermMap array_vals = gs->get_array_values(arr, const_base);
  if (const_base)
  {
    EXPECT_EQ(const_base->get_sort(), elemsort);
  }

  // How many stores a binary needs is its own business -- one that picks a
  // constant base equal to a required value lists one index where another
  // lists two -- so read each constrained index out of the entry the model
  // listed, or the base standing in for every index it did not.
  auto value_at = [&array_vals, &const_base](const Term & idx) {
    auto entry = array_vals.find(idx);
    return entry == array_vals.end() ? const_base : entry->second;
  };
  EXPECT_EQ(value_at(one), eleven);
  EXPECT_EQ(value_at(two), twelve);
  gs->pop(1);
}

TEST_P(GenericSolverArrayModelTests, SelectMadeAfterCheckSat)
{
  Sort idxsort = gs->make_sort(BV, 4);
  Sort elemsort = gs->make_sort(BV, 8);
  Term arr = gs->make_symbol("arr", gs->make_sort(ARRAY, idxsort, elemsort));
  Term one = gs->make_term(1, idxsort);
  Term eleven = gs->make_term(11, elemsort);
  gs->assert_formula(
      gs->make_term(Equal, gs->make_term(Select, arr, one), eleven));
  ASSERT_TRUE(gs->check_sat().is_sat());

  Term const_base;
  UnorderedTermMap array_vals = gs->get_array_values(arr, const_base);
  // a select made after the check, at an index nothing constrains, reads
  // what the model gives there: an entry it lists, or else its base
  Term two = gs->make_term(2, idxsort);
  auto entry = array_vals.find(two);
  EXPECT_EQ(gs->get_value(gs->make_term(Select, arr, two)),
            entry == array_vals.end() ? const_base : entry->second);
}

TEST_P(GenericSolverUfTests, SortMadeAfterCheckSat)
{
  Term b = gs->make_symbol("b", gs->make_sort(BOOL));
  gs->assert_formula(b);
  ASSERT_TRUE(gs->check_sat().is_sat());
  Sort u_sort = gs->make_sort("U", 0);
  Term u = gs->make_symbol("u", u_sort);
  // the model is still the one the check found
  EXPECT_EQ(gs->get_value(b), gs->make_term(true));
  // the sort goes to the binary ahead of the symbol, as both do ahead of
  // the next assertion
  gs->assert_formula(gs->make_term(Equal, u, u));
}

TEST_P(GenericSolverDatatypeTests, DatatypeMadeAfterCheckSat)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", bv_sort);
  Term three = gs->make_term(3, bv_sort);
  gs->assert_formula(gs->make_term(Equal, x, three));
  ASSERT_TRUE(gs->check_sat().is_sat());
  DatatypeDecl box_decl = gs->make_datatype_decl("box");
  DatatypeConstructorDecl mkbox = gs->make_datatype_constructor_decl("mkbox");
  gs->add_selector(mkbox, "content", bv_sort);
  gs->add_constructor(box_decl, mkbox);
  Sort box_sort = gs->make_sort(box_decl);
  Term boxed = gs->make_term(
      Apply_Constructor, gs->get_constructor(box_sort, "mkbox"), three);
  Term content = gs->make_term(
      Apply_Selector, gs->get_selector(box_sort, "mkbox", "content"), boxed);
  EXPECT_EQ(gs->get_value(x), three);
  // content has a sort the model knows, but goes through one it does not
  EXPECT_THROW(gs->get_value(content), IncorrectUsageException);
  ASSERT_TRUE(gs->check_sat().is_sat());
  EXPECT_EQ(gs->get_value(content), three);
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
  // whichever notation the binary answers in, the value read back is
  // the same literal make_term writes
  EXPECT_EQ(gs->get_value(i1), bv_zero);
  gs->pop(1);
}

TEST_P(GenericSolverTests, ValueOfTermMadeAfterCheckSat)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", bv_sort);
  Term y = gs->make_symbol("y", bv_sort);
  gs->assert_formula(gs->make_term(Equal, x, gs->make_term(3, bv_sort)));
  gs->assert_formula(gs->make_term(Equal, y, gs->make_term(4, bv_sort)));
  ASSERT_TRUE(gs->check_sat().is_sat());
  // made after the check, as is the term built on it
  Term sum = gs->make_term(BVAdd, x, y);
  Term doubled = gs->make_term(BVAdd, sum, sum);
  EXPECT_EQ(gs->get_value(sum), gs->make_term(7, bv_sort));
  EXPECT_EQ(gs->get_value(doubled), gs->make_term(14, bv_sort));
  // the model read is still the one the check found
  EXPECT_EQ(gs->get_value(x), gs->make_term(3, bv_sort));
}

TEST_P(GenericSolverTests, TermMadeAfterCheckSatCanBeAsserted)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", bv_sort);
  Term three = gs->make_term(3, bv_sort);
  gs->assert_formula(gs->make_term(Equal, x, three));
  ASSERT_TRUE(gs->check_sat().is_sat());
  Term x_is_not_three = gs->make_term(Not, gs->make_term(Equal, x, three));
  EXPECT_EQ(gs->get_value(x_is_not_three), gs->make_term(false));
  gs->assert_formula(x_is_not_three);
  EXPECT_TRUE(gs->check_sat().is_unsat());
}

TEST_P(GenericSolverTests, TermMadeAfterCheckSatCanBeAssumed)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", bv_sort);
  Term three = gs->make_term(3, bv_sort);
  gs->assert_formula(gs->make_term(Equal, x, three));
  ASSERT_TRUE(gs->check_sat().is_sat());
  Term x_is_not_three = gs->make_term(Not, gs->make_term(Equal, x, three));
  EXPECT_TRUE(gs->check_sat_assuming({ x_is_not_three }).is_unsat());
}

TEST_P(GenericSolverTests, GetValueOutsideSatModeThrows)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", bv_sort);
  // no check yet
  EXPECT_THROW(gs->get_value(x), IncorrectUsageException);
  gs->assert_formula(gs->make_term(Equal, x, gs->make_term(3, bv_sort)));
  ASSERT_TRUE(gs->check_sat().is_sat());
  // a push leaves the sat mode
  gs->push(1);
  EXPECT_THROW(gs->get_value(x), IncorrectUsageException);
  gs->assert_formula(gs->make_term(Not, gs->make_term(Equal, x, x)));
  ASSERT_TRUE(gs->check_sat().is_unsat());
  EXPECT_THROW(gs->get_value(x), IncorrectUsageException);
}

TEST_P(GenericSolverTests, SymbolMadeAfterCheckSat)
{
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", bv_sort);
  Term three = gs->make_term(3, bv_sort);
  gs->assert_formula(gs->make_term(Equal, x, three));
  ASSERT_TRUE(gs->check_sat().is_sat());
  Term y = gs->make_symbol("y", bv_sort);
  // the model is still the one the check found
  EXPECT_EQ(gs->get_value(x), three);
  // but it has no value for a symbol declared since
  EXPECT_THROW(gs->get_value(y), IncorrectUsageException);
  EXPECT_THROW(gs->get_value(gs->make_term(BVAdd, x, y)),
               IncorrectUsageException);
  // the next assertion declares it
  gs->assert_formula(gs->make_term(Equal, y, x));
  ASSERT_TRUE(gs->check_sat().is_sat());
  EXPECT_EQ(gs->get_value(y), three);
}

TEST_P(GenericSolverTests, GetUnsatAssumptionsOutsideUnsatModeThrows)
{
  Term b = gs->make_symbol("b", gs->make_sort(BOOL));
  ASSERT_TRUE(gs->check_sat_assuming({ b }).is_sat());
  UnorderedTermSet core;
  EXPECT_THROW(gs->get_unsat_assumptions(core), IncorrectUsageException);
}

TEST_P(GenericSolverTests, StartOnlyOptionAfterLogicThrows)
{
  // the fixture has set the logic
  EXPECT_THROW(gs->set_opt("produce-models", "true"), IncorrectUsageException);
}

TEST_P(GenericSolverTests, SecondSetLogicIsLeftToTheBinary)
{
  // the fixture has set the logic
  if (accepts_second_logic(binary))
  {
    EXPECT_NO_THROW(gs->set_logic("ALL"));
  }
  else
  {
    EXPECT_THROW(gs->set_logic("ALL"), IncorrectUsageException);
  }
  gs->assert_formula(gs->make_term(false));
  EXPECT_TRUE(gs->check_sat().is_unsat());
}

TEST_P(GenericSolverTests, DeclarationWithoutLogic)
{
  start_binary();
  // still in start mode, which this option needs
  gs->set_opt("produce-models", "true");
  Sort bv_sort = gs->make_sort(BV, 4);
  Term three = gs->make_term(3, bv_sort);
  Term x = gs->make_symbol("x", bv_sort);
  gs->assert_formula(gs->make_term(Equal, x, three));
  ASSERT_TRUE(gs->check_sat().is_sat());
  EXPECT_EQ(gs->get_value(x), three);
}

TEST_P(GenericSolverTests, SetLogicAfterDeclarationIsLeftToTheBinary)
{
  start_binary();
  gs->set_opt("produce-models", "true");
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", bv_sort);
  if (accepts_logic_after_declaration(binary))
  {
    EXPECT_NO_THROW(gs->set_logic("QF_BV"));
  }
  else
  {
    EXPECT_THROW(gs->set_logic("QF_BV"), IncorrectUsageException);
  }
  Term three = gs->make_term(3, bv_sort);
  gs->assert_formula(gs->make_term(Equal, x, three));
  ASSERT_TRUE(gs->check_sat().is_sat());
  EXPECT_EQ(gs->get_value(x), three);
}

TEST_P(GenericSolverRealTests, RealStringModels)
{
  Sort real_sort = gs->make_sort(REAL);
  EXPECT_EQ(gs->make_term("5", real_sort), gs->make_term(5, real_sort));
  EXPECT_EQ(gs->make_term("-5", real_sort), gs->make_term(-5, real_sort));
  Term minus_half = gs->make_term("-2.5", real_sort);
  EXPECT_EQ(minus_half->to_string(), "(- 2.5)");
  Term r = gs->make_symbol("r", real_sort);
  Term sum = gs->make_term(Plus, minus_half, gs->make_term("5", real_sort));
  gs->assert_formula(gs->make_term(Equal, r, sum));
  gs->assert_formula(gs->make_term(
      Not, gs->make_term(Equal, r, gs->make_term("2.5", real_sort))));
  EXPECT_TRUE(gs->check_sat().is_unsat());
}

TEST_P(GenericSolverRealTests, RealStringFractions)
{
  Sort real_sort = gs->make_sort(REAL);
  Term half = gs->make_term(
      Div, gs->make_term(1, real_sort), gs->make_term(2, real_sort));
  Term minus_half = gs->make_term(
      Div, gs->make_term(-1, real_sort), gs->make_term(2, real_sort));
  // the second as TermTranslator writes a fraction
  for (const auto & [val, expected] :
       { std::pair<const char *, Term>{ "1/2", half },
         { "1 / 2", half },
         { "-1/2", minus_half } })
  {
    SCOPED_TRACE(val);
    gs->push(1);
    gs->assert_formula(gs->make_term(
        Not, gs->make_term(Equal, gs->make_term(val, real_sort), expected)));
    EXPECT_TRUE(gs->check_sat().is_unsat());
    gs->pop(1);
  }
}

TEST_P(GenericSolverRealTests, RealStringNotANumber)
{
  Sort real_sort = gs->make_sort(REAL);
  gs->make_symbol("x", real_sort);
  for (const char * val : { "x", "-x", ".5", "1.", "1/", "", "1/0" })
  {
    EXPECT_THROW(gs->make_term(val, real_sort), IncorrectUsageException)
        << "for \"" << val << "\"";
  }
}

TEST_P(GenericSolverTests, BvValueLiterals)
{
  Sort bv_sort = gs->make_sort(BV, 8);
  // every way of making the same value gives one literal of the width
  Term value = gs->make_term(-0b100, bv_sort);
  EXPECT_EQ(value->to_string(), "#b11111100");
  EXPECT_EQ(gs->make_term(0b1111'1100, bv_sort), value);
  EXPECT_EQ(gs->make_term(std::to_string(-0b100), bv_sort), value);
  EXPECT_EQ(gs->make_term(std::to_string(0b1111'1100), bv_sort), value);
  EXPECT_EQ(gs->make_term("11111100", bv_sort, 2), value);
  EXPECT_EQ(gs->make_term("-100", bv_sort, 2), value);
  EXPECT_EQ(gs->make_term("FC", bv_sort, 16), value);
  EXPECT_EQ(gs->make_term("-4", bv_sort, 16), value);
  EXPECT_EQ(gs->make_term("1", bv_sort, 2)->to_string(), "#b00000001");
  // a negative value is a value too, and reads back as itself
  EXPECT_TRUE(value->is_value());
  EXPECT_EQ(value->to_signed_int(), -0b100);
  Term b = gs->make_symbol("b", bv_sort);
  gs->assert_formula(gs->make_term(Equal, b, value));
  ASSERT_TRUE(gs->check_sat().is_sat());
  EXPECT_EQ(gs->get_value(b), value);
}

TEST_P(GenericSolverTests, BvStringOutOfRange)
{
  Sort bv_sort = gs->make_sort(BV, 8);
  EXPECT_EQ(gs->make_term(std::to_string(0b1111'1111), bv_sort)->to_string(),
            "#b11111111");
  EXPECT_EQ(gs->make_term(std::to_string(-0b1000'0000), bv_sort)->to_string(),
            "#b10000000");
  EXPECT_EQ(gs->make_term("-10000000", bv_sort, 2)->to_string(), "#b10000000");
  EXPECT_EQ(gs->make_term("-80", bv_sort, 16)->to_string(), "#b10000000");
  EXPECT_THROW(gs->make_term(std::to_string(0b1'0000'0000), bv_sort),
               IncorrectUsageException);
  EXPECT_THROW(gs->make_term(std::to_string(-0b1000'0001), bv_sort),
               IncorrectUsageException);
  EXPECT_THROW(gs->make_term("100000000", bv_sort, 2), IncorrectUsageException);
  EXPECT_THROW(gs->make_term("-10000001", bv_sort, 2), IncorrectUsageException);
  EXPECT_THROW(gs->make_term("100", bv_sort, 16), IncorrectUsageException);
  EXPECT_THROW(gs->make_term("-81", bv_sort, 16), IncorrectUsageException);
  // the rejected values never reach the binary, which still answers
  Term b = gs->make_symbol("b", bv_sort);
  gs->assert_formula(gs->make_term(
      Equal, b, gs->make_term(std::to_string(0b1111'1111), bv_sort)));
  EXPECT_TRUE(gs->check_sat().is_sat());
}

TEST_P(GenericSolverTests, BvStringNotANumeral)
{
  Sort bv_sort = gs->make_sort(BV, 8);
  for (const char * val : { "", "-", "+5", "--5", " 5", "5 ", "1a", "abc" })
  {
    EXPECT_THROW(gs->make_term(val, bv_sort), IncorrectUsageException)
        << "for \"" << val << "\"";
  }
  EXPECT_THROW(gs->make_term("", bv_sort, 2), IncorrectUsageException);
  EXPECT_THROW(gs->make_term("102", bv_sort, 2), IncorrectUsageException);
  EXPECT_THROW(gs->make_term("fg", bv_sort, 16), IncorrectUsageException);
  // the rejected strings never reach the binary, which still answers
  Term b = gs->make_symbol("b", bv_sort);
  gs->assert_formula(
      gs->make_term(Equal, b, gs->make_term(std::to_string(0b101), bv_sort)));
  EXPECT_TRUE(gs->check_sat().is_sat());
}

TEST_P(GenericSolverTests, BvStringWideBounds)
{
  Sort bv64 = gs->make_sort(BV, 64);
  EXPECT_EQ(gs->make_term(std::to_string(UINT64_MAX), bv64)->to_string(),
            "#b" + string(64, '1'));
  EXPECT_EQ(gs->make_term(std::to_string(INT64_MIN), bv64)->to_string(),
            "#b1" + string(63, '0'));
  // the values from here on are too wide for C++ literals
  // 2^64
  EXPECT_THROW(gs->make_term("18446744073709551616", bv64),
               IncorrectUsageException);
  // -(2^63 + 1)
  EXPECT_THROW(gs->make_term("-9223372036854775809", bv64),
               IncorrectUsageException);
  Sort bv65 = gs->make_sort(BV, 65);
  // 2^65 - 1
  EXPECT_EQ(gs->make_term("36893488147419103231", bv65)->to_string(),
            "#b" + string(65, '1'));
  // -2^64
  EXPECT_EQ(gs->make_term("-18446744073709551616", bv65)->to_string(),
            "#b1" + string(64, '0'));
  // 2^65
  EXPECT_THROW(gs->make_term("36893488147419103232", bv65),
               IncorrectUsageException);
  // -(2^64 + 1)
  EXPECT_THROW(gs->make_term("-18446744073709551617", bv65),
               IncorrectUsageException);
}

TEST_P(GenericSolverTests, BvIntOutOfRange)
{
  Sort bv_sort = gs->make_sort(BV, 8);
  EXPECT_THROW(gs->make_term(0b1'0000'0000, bv_sort), IncorrectUsageException);
  EXPECT_THROW(gs->make_term(-0b1000'0001, bv_sort), IncorrectUsageException);
  Sort bv64 = gs->make_sort(BV, 64);
  EXPECT_EQ(gs->make_term(INT64_MIN, bv64)->to_string(),
            "#b1" + string(63, '0'));
  EXPECT_EQ(gs->make_term(INT64_MAX, bv64)->to_string(),
            "#b0" + string(63, '1'));
}

TEST_P(GenericSolverIntTests, IntStringNotANumber)
{
  Sort int_sort = gs->make_sort(INT);
  gs->make_symbol("x", int_sort);
  // each would reach the binary as the symbol x, or as a decimal
  for (const char * val : { "x", "-x", "1.5", "" })
  {
    EXPECT_THROW(gs->make_term(val, int_sort), IncorrectUsageException)
        << "for \"" << val << "\"";
  }
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

TEST_P(GenericSolverTests, AssumeForeignTerm)
{
  // a symbol made outside this solver, which never declared it
  Term foreign = std::make_shared<GenericTerm>(
      gs->make_sort(BOOL), Op(), TermVec{}, "|foreign|", true);
  EXPECT_THROW(gs->check_sat_assuming({ foreign }), IncorrectUsageException);
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

TEST_P(GenericSolverTests, FormulaAssumptions)
{
  gs->push(1);
  Sort bv_sort = gs->make_sort(BV, 4);
  Term x = gs->make_symbol("x", bv_sort);
  Term y = gs->make_symbol("y", bv_sort);
  Term x_lt_y = gs->make_term(BVUlt, x, y);
  Term x_ge_y = gs->make_term(BVUge, x, y);
  EXPECT_TRUE(gs->check_sat_assuming({ x_lt_y }).is_sat());
  ASSERT_TRUE(gs->check_sat_assuming({ x_lt_y, x_ge_y }).is_unsat());
  UnorderedTermSet core;
  gs->get_unsat_assumptions(core);
  // each assumption is satisfiable on its own, so the core needs both
  EXPECT_EQ(core, (UnorderedTermSet{ x_lt_y, x_ge_y }));
  gs->pop(1);
  // the assumptions are still accepted once the scope they were made in
  // is gone
  EXPECT_TRUE(gs->check_sat_assuming({ x_lt_y }).is_sat());
  EXPECT_TRUE(gs->check_sat_assuming({ x_lt_y, x_ge_y }).is_unsat());
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

INSTANTIATE_TEST_SUITE_P(,
                         GenericSolverRealTests,
                         testing::ValuesIn(params_with(THEORY_REAL)),
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

INSTANTIATE_TEST_SUITE_P(,
                         GenericSolverArrayModelTests,
                         testing::ValuesIn(params_with(ARRAY_MODELS)),
                         param_name);

INSTANTIATE_TEST_SUITE_P(,
                         GenericSolverDatatypeTests,
                         testing::ValuesIn(params_with(THEORY_DATATYPE)),
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

TEST(GenericSolver, StderrIsNotAnAnswer)
{
  // the binary writes a diagnostic to stderr ahead of its answer, as
  // Bitwuzla warns ahead of some check-sat answers
  SmtSolver gs = std::make_shared<GenericSolver>(
      "/bin/sh",
      vector<string>{ "-c",
                      "while read -r line; do case \"$line\" in"
                      " *check-sat*) echo 'stderr is not an answer' >&2;"
                      " echo sat ;;"
                      " *) echo success ;; esac; done" },
      solver_response_timeout,
      5);
  EXPECT_TRUE(gs->check_sat().is_sat());
}

}  // namespace smt_tests
