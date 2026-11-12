/*!
 * \file test-smtlib-reader.cpp
 * \brief Tests the SmtLibReader.
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * The benchmarks under tests/smt2 state the answer to each check-sat with a
 * (set-info :status ...) before it, as SMT-LIB's incremental benchmarks do.
 */

#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <memory>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/smtlib_reader.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "test_paths.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

/** Checks the answer to each check-sat against the (set-info :status ...)
 *  before it, failing the test for a check-sat without one
 */
class StatusChecker : public SmtLibReader
{
 public:
  using SmtLibReader::SmtLibReader;

  void set_info(const string & key, const string & val) override
  {
    if (key == "status")
    {
      expected_ = val;
    }
  }

  Result check_sat() override { return checked(solver_->check_sat()); }

  Result check_sat_assuming(const TermVec & assumptions) override
  {
    return checked(solver_->check_sat_assuming(assumptions));
  }

  /** The number of check-sats answered */
  size_t checks() const { return checks_; }

  /** A status no check-sat has followed, or empty */
  const string & pending_status() const { return expected_; }

 private:
  Result checked(Result r)
  {
    ++checks_;
    EXPECT_EQ(r.to_string(), expected_) << "at check-sat " << checks_;
    expected_.clear();
    return r;
  }

  string expected_;
  size_t checks_ = 0;
};

/** The .smt2 inputs in a directory of the test resources, in name order */
vector<string> inputs_in(const string & directory)
{
  vector<string> inputs;
  for (const filesystem::directory_entry & entry :
       filesystem::directory_iterator(string(smt_tests::smtlib_resource_dir)
                                      + "/" + directory))
  {
    if (entry.path().extension() == ".smt2")
    {
      inputs.push_back(entry.path().string());
    }
  }
  sort(inputs.begin(), inputs.end());
  return inputs;
}

// (configuration, input, whether the reader is strict)
typedef tuple<SolverConfiguration, string, bool> ReaderInput;

string reader_input_name(const testing::TestParamInfo<ReaderInput> & info)
{
  string file = filesystem::path(get<1>(info.param)).stem().string();
  // the inputs are named test-..., which says nothing in a test name
  if (file.rfind("test-", 0) == 0)
  {
    file.erase(0, 5);
  }
  string name = config_name(get<0>(info.param)) + "_" + file;
  replace(name.begin(), name.end(), '-', '_');
  return name;
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Benchmark);
class Benchmark : public ::testing::TestWithParam<ReaderInput>
{
};

TEST_P(Benchmark, Answers)
{
  const auto & [config, input, strict] = GetParam();
  if (config.solver_enum == YICES2
      && filesystem::path(input).filename() == "test-array.smt2")
  {
    GTEST_SKIP() << "Yices2 cannot read an array constrained to equal a "
                    "constant array, which test-array.smt2 does";
  }
  if (config.solver_enum == BZLA
      && filesystem::path(input).filename()
             == "test-uninterp-sort-zero-arity.smt2")
  {
    GTEST_SKIP() << "Bitwuzla answers unknown to the distinct and the "
                    "disjunctions of equalities over an uninterpreted sort in "
                    "test-uninterp-sort-zero-arity.smt2";
  }
  SmtSolver s = create_solver(config);
  s->set_opt("produce-models", "true");
  StatusChecker reader(s, strict);
  reader.parse(input);
  EXPECT_GT(reader.checks(), 0u);
  EXPECT_EQ(reader.pending_status(), "");
}

// The inputs follow SMT-LIB, so a strict reader reads them, except those
// of qf_lira_nonstrict, which use its extensions.
INSTANTIATE_TEST_SUITE_P(
    QF_UFLIA,
    Benchmark,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_INT })),
                     testing::ValuesIn(inputs_in("qf_uflia")),
                     testing::Values(true)),
    reader_input_name);

INSTANTIATE_TEST_SUITE_P(
    QF_LRA,
    Benchmark,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_REAL })),
                     testing::ValuesIn(inputs_in("qf_lra")),
                     testing::Values(true)),
    reader_input_name);

INSTANTIATE_TEST_SUITE_P(
    QF_S,
    Benchmark,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_INT, THEORY_STR })),
                     testing::ValuesIn(inputs_in("qf_s")),
                     testing::Values(true)),
    reader_input_name);

INSTANTIATE_TEST_SUITE_P(
    QF_UFBV,
    Benchmark,
    testing::Combine(
        testing::ValuesIn(available_non_generic_solver_configurations()),
        testing::ValuesIn(inputs_in("qf_ufbv")),
        testing::Values(true)),
    reader_input_name);

INSTANTIATE_TEST_SUITE_P(
    QF_ALIA,
    Benchmark,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_INT, ARRAY_MODELS, CONSTARR })),
                     testing::ValuesIn(inputs_in("qf_alia")),
                     testing::Values(true)),
    reader_input_name);

INSTANTIATE_TEST_SUITE_P(
    QF_UF,
    Benchmark,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { UNINTERP_SORT })),
                     testing::ValuesIn(inputs_in("qf_uf")),
                     testing::Values(true)),
    reader_input_name);

INSTANTIATE_TEST_SUITE_P(
    QF_UF_PARAM_SORTS,
    Benchmark,
    testing::Combine(testing::ValuesIn(filter_solver_configurations(
                         { PARAM_UNINTERP_SORT, THEORY_INT })),
                     testing::ValuesIn(inputs_in("qf_uf_param_sorts")),
                     testing::Values(true)),
    reader_input_name);

INSTANTIATE_TEST_SUITE_P(
    QF_LIRA,
    Benchmark,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_INT, THEORY_REAL })),
                     testing::ValuesIn(inputs_in("qf_lira")),
                     testing::Values(true)),
    reader_input_name);

INSTANTIATE_TEST_SUITE_P(
    QF_LIRA_NONSTRICT,
    Benchmark,
    testing::Combine(testing::ValuesIn(filter_non_generic_solver_configurations(
                         { THEORY_INT, THEORY_REAL })),
                     testing::ValuesIn(inputs_in("qf_lira_nonstrict")),
                     testing::Values(false)),
    reader_input_name);

/** Records the answer to the last check-sat */
class AnswerRecorder : public SmtLibReader
{
 public:
  using SmtLibReader::SmtLibReader;

  Result check_sat() override
  {
    answer = solver_->check_sat();
    return answer;
  }

  Result answer;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Dump);
class Dump : public ::testing::Test,
             public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("incremental", "true");
  }

  /** Makes x and y, after any set_logic, which some solvers refuse once
   *  they have made a term
   */
  void make_symbols()
  {
    Sort bvsort = s->make_sort(BV, 4);
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
  }

  /** What a fresh solver of the same configuration answers to the
   *  check-sat that ends s's dump
   *  @param name what tells the dump apart from the other tests' dumps
   */
  Result reread(const string & name)
  {
    string file =
        testing::TempDir() + "dump-" + name + "-" + config_name(GetParam());
    s->dump_smt2(file);
    SmtSolver fresh = create_solver(GetParam());
    AnswerRecorder reader(fresh);
    reader.parse(file);
    return reader.answer;
  }

  SmtSolver s;
  Term x, y;
};

TEST_P(Dump, KeepsTheLogicAndTheAssertions)
{
  s->set_logic("QF_BV");
  make_symbols();
  s->assert_formula(s->make_term(Equal, x, y));
  s->assert_formula(s->make_term(Distinct, x, y));
  EXPECT_TRUE(reread("assertions").is_unsat());
}

TEST_P(Dump, KeepsAssertionsMadeInAPush)
{
  make_symbols();
  s->push();
  s->assert_formula(s->make_term(Equal, x, y));
  s->assert_formula(s->make_term(Distinct, x, y));
  EXPECT_TRUE(reread("pushed").is_unsat());
}

TEST_P(Dump, LeavesOutPoppedAssertions)
{
  make_symbols();
  s->assert_formula(s->make_term(Equal, x, y));
  s->push();
  s->assert_formula(s->make_term(Distinct, x, y));
  s->pop();
  EXPECT_TRUE(reread("popped").is_sat());
}

TEST_P(Dump, LeavesOutResetAssertions)
{
  if (GetParam().solver_enum == BTOR)
  {
    // Boolector resets assertions only with this option
    s->set_opt("base-context-1", "true");
  }
  make_symbols();
  s->assert_formula(s->make_term(Distinct, x, y));
  s->reset_assertions();
  s->assert_formula(s->make_term(Equal, x, y));
  EXPECT_TRUE(reread("reset").is_sat());
}

INSTANTIATE_TEST_SUITE_P(SmtLibReader,
                         Dump,
                         testing::ValuesIn(available_solver_configurations()),
                         ConfigName());

// Two distinct sorts named S, so that the dump renames one. The other
// assertions check that renaming does not change how the rest of the dump
// is written.
GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(DumpRenamedSorts);
class DumpRenamedSorts : public Dump
{
 protected:
  void SetUp() override
  {
    Dump::SetUp();
    if (GetParam().solver_enum == GENERIC_SOLVER)
    {
      GTEST_SKIP()
          << "the generic solver refuses to declare a second sort with "
             "the same name";
    }
    if (GetParam().solver_enum == BZLA)
    {
      GTEST_SKIP() << "Bitwuzla answers unknown to distinct over an "
                      "uninterpreted sort";
    }
    s->set_logic("QF_AUFBV");
    Sort first = s->make_sort("S", 0);
    Sort second = s->make_sort("S", 0);
    if (first == second)
    {
      GTEST_SKIP() << "this solver returns the existing sort when one with the "
                      "same name is declared again";
    }
    make_symbols();
    Sort bvsort = x->get_sort();
    b = s->make_symbol("b", second);
    b2 = s->make_symbol("b2", second);
    arr = s->make_symbol("arr", s->make_sort(ARRAY, second, bvsort));
    Term f =
        s->make_symbol("f", s->make_sort(FUNCTION, SortVec{ second, bvsort }));
    Term p = s->make_symbol("p", s->make_sort(BOOL));
    Term q = s->make_symbol("q", s->make_sort(BOOL));
    Term r = s->make_symbol("r", s->make_sort(BOOL));

    s->assert_formula(s->make_term(Distinct, b, b2));
    s->assert_formula(s->make_term(Equal, s->make_term(BVMul, x, x), y));
    s->assert_formula(s->make_term(Equal,
                                   s->make_term(Op(Extract, 1, 0), x),
                                   s->make_term(Op(Extract, 3, 2), y)));
    s->assert_formula(s->make_term(
        Distinct, s->make_term(BVAnd, x, y), s->make_term(BVOr, x, y)));
    s->assert_formula(s->make_term(
        Equal, s->make_term(Select, s->make_term(Store, arr, b, x), b2), y));
    s->assert_formula(s->make_term(
        Distinct, s->make_term(Apply, f, b), s->make_term(Apply, f, b2)));
    s->assert_formula(s->make_term(Or, s->make_term(And, p, q, r), q));
    s->assert_formula(s->make_term(
        Distinct, s->make_symbol("a", first), s->make_symbol("a2", first)));
  }

  Term b, b2, arr;
};

// x = 4 and y = 0 satisfy the assertions
TEST_P(DumpRenamedSorts, KeepsASatisfiableQuery)
{
  EXPECT_TRUE(reread("renamed-sat").is_sat());
  EXPECT_TRUE(s->check_sat().is_sat());
}

// reading x back from where it was stored makes it y, which it is not
TEST_P(DumpRenamedSorts, KeepsAnUnsatisfiableQuery)
{
  s->assert_formula(s->make_term(
      Equal, s->make_term(Select, s->make_term(Store, arr, b, x), b), y));
  s->assert_formula(s->make_term(Distinct, x, y));
  EXPECT_TRUE(reread("renamed-unsat").is_unsat());
  EXPECT_TRUE(s->check_sat().is_unsat());
}

INSTANTIATE_TEST_SUITE_P(
    SmtLibReader,
    DumpRenamedSorts,
    testing::ValuesIn(filter_solver_configurations({ UNINTERP_SORT })),
    ConfigName());

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(DumpUninterpretedSort);
class DumpUninterpretedSort : public Dump
{
};

// The dump must declare S for a and f to read back.
TEST_P(DumpUninterpretedSort, DeclaresTheSort)
{
  make_symbols();
  Sort sort = s->make_sort("S", 0);
  Term a = s->make_symbol("a", sort);
  Term f = s->make_symbol(
      "f", s->make_sort(FUNCTION, SortVec{ sort, x->get_sort() }));
  Term fa = s->make_term(Apply, f, a);
  s->assert_formula(s->make_term(Equal, fa, x));
  s->assert_formula(s->make_term(Distinct, fa, x));
  EXPECT_TRUE(reread("uninterpreted").is_unsat());
}

INSTANTIATE_TEST_SUITE_P(
    SmtLibReader,
    DumpUninterpretedSort,
    testing::ValuesIn(filter_solver_configurations({ UNINTERP_SORT })),
    ConfigName());

TEST(UnorderedScopedSymbolMap, PopOutermostScope)
{
  UnorderedScopedSymbolMap map;
  EXPECT_THROW(map.pop_scope(), IncorrectUsageException);
  map.push_scope();
  EXPECT_NO_THROW(map.pop_scope());
  EXPECT_THROW(map.pop_scope(), IncorrectUsageException);
  EXPECT_EQ(map.current_scope(), 0u);
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Scopes);
class Scopes : public ::testing::Test,
               public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("incremental", "true");
    reader = std::make_unique<SmtLibReader>(s);
    bvsort = s->make_sort(BV, 4);
  }

  SmtSolver s;
  std::unique_ptr<SmtLibReader> reader;
  Sort bvsort;
};

TEST_P(Scopes, PopWithoutPush)
{
  EXPECT_THROW(reader->pop(), IncorrectUsageException);
  EXPECT_THROW(reader->pop_scope(), IncorrectUsageException);
  reader->push();
  EXPECT_NO_THROW(reader->pop());
  EXPECT_THROW(reader->pop(), IncorrectUsageException);
}

TEST_P(Scopes, BindOutsideScope)
{
  Term t = s->make_symbol("t", bvsort);
  EXPECT_THROW(reader->register_arg("x", bvsort), IncorrectUsageException);
  EXPECT_THROW(reader->create_param("y", bvsort), IncorrectUsageException);
  EXPECT_THROW(reader->let_binding("z", t), IncorrectUsageException);
  reader->push_scope();
  EXPECT_NO_THROW(reader->register_arg("x", bvsort));
  EXPECT_NO_THROW(reader->let_binding("z", t));
  EXPECT_NO_THROW(reader->pop_scope());
}

TEST_P(Scopes, ShadowedBinding)
{
  Term outer = s->make_symbol("outer", bvsort);
  Term inner = s->make_symbol("inner", bvsort);
  reader->push_scope();
  reader->let_binding("z", outer);
  EXPECT_THROW(reader->let_binding("z", inner), IncorrectUsageException);
  reader->push_scope();
  reader->let_binding("z", inner);
  EXPECT_EQ(reader->lookup_symbol("z"), inner);
  reader->pop_scope();
  EXPECT_EQ(reader->lookup_symbol("z"), outer);
  reader->pop_scope();
  EXPECT_FALSE(reader->lookup_symbol("z"));
}

TEST_P(Scopes, DefineOverOuterSymbol)
{
  reader->new_symbol("x", bvsort);
  reader->push();
  EXPECT_THROW(reader->define_fun("x", s->make_term(1, bvsort)),
               IncorrectUsageException);
}

INSTANTIATE_TEST_SUITE_P(
    SmtLibReader,
    Scopes,
    testing::ValuesIn(available_non_generic_solver_configurations()),
    ConfigName());

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Input);
class Input : public ::testing::Test,
              public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    reader = std::make_unique<SmtLibReader>(s);
  }

  static string error_input(const string & name)
  {
    return string(smt_tests::smtlib_resource_dir) + "/errors/" + name;
  }

  /** Parses an input from errors/ and returns the message of the
   *  SmtLibParseException it throws, failing the test if it throws none */
  string parse_error(const string & name)
  {
    try
    {
      reader->parse(error_input(name));
    }
    catch (const SmtLibParseException & e)
    {
      return e.what();
    }
    ADD_FAILURE() << name << " parsed without an SmtLibParseException";
    return "";
  }

  SmtSolver s;
  std::unique_ptr<SmtLibReader> reader;
};

TEST_P(Input, MissingFile)
{
  EXPECT_THROW(reader->parse("no-such-directory/no-such-file.smt2"),
               IncorrectUsageException);
}

TEST_P(Input, UnreadableFile)
{
  EXPECT_THROW(reader->parse(string(smt_tests::smtlib_resource_dir)),
               std::runtime_error);
}

TEST_P(Input, SyntaxError)
{
  const string message = parse_error("syntax-error.smt2");
  EXPECT_EQ(message.rfind(error_input("syntax-error.smt2") + ":3.", 0), 0u)
      << message;
}

TEST_P(Input, OutOfRangeNumeral)
{
  const string message = parse_error("out-of-range-numeral.smt2");
  EXPECT_EQ(message.rfind(error_input("out-of-range-numeral.smt2") + ":2.", 0),
            0u)
      << message;
}

TEST_P(Input, Redeclaration)
{
  const string message = parse_error("redeclaration.smt2");
  EXPECT_EQ(message.rfind(error_input("redeclaration.smt2") + ":3.", 0), 0u)
      << message;
}

TEST_P(Input, PopWithoutPush)
{
  const string message = parse_error("pop-without-push.smt2");
  EXPECT_EQ(message.rfind(error_input("pop-without-push.smt2") + ":2.", 0), 0u)
      << message;
}

TEST_P(Input, ShortArraySort)
{
  const string message = parse_error("short-array-sort.smt2");
  EXPECT_EQ(message.rfind(error_input("short-array-sort.smt2") + ":2.", 0), 0u)
      << message;
}

TEST_P(Input, FailedParseClosesScopes)
{
  // the error comes inside the define-fun, with its argument b in scope
  EXPECT_THROW(reader->parse(error_input("failed-define-fun.smt2")),
               SmtLibParseException);
  EXPECT_EQ(reader->current_scope(), 0u);
  const string message = parse_error("stale-argument.smt2");
  EXPECT_NE(message.find("Unrecognized symbol: b"), string::npos) << message;
}

TEST_P(Input, ArrayLogic)
{
  if (GetParam().solver_enum == BTOR)
  {
    GTEST_SKIP() << "Boolector refuses the logic QF_AX";
  }
  EXPECT_NO_THROW(reader->set_logic("QF_AX"));
}

TEST_P(Input, EmptyApplication)
{
  EXPECT_THROW(reader->parse(error_input("empty-application.smt2")),
               SmtLibParseException);
}

TEST_P(Input, UnknownSymbol)
{
  EXPECT_THROW(reader->parse(error_input("unknown-symbol.smt2")),
               SmtLibParseException);
}

TEST_P(Input, UnknownCharacter)
{
  EXPECT_THROW(reader->parse(error_input("unknown-character.smt2")),
               SmtLibParseException);
}

INSTANTIATE_TEST_SUITE_P(
    SmtLibReader,
    Input,
    testing::ValuesIn(available_non_generic_solver_configurations()),
    ConfigName());

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Logics);
class Logics : public ::testing::Test,
               public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    reader = std::make_unique<SmtLibReader>(s);
  }

  SmtSolver s;
  std::unique_ptr<SmtLibReader> reader;
};

TEST_P(Logics, AllLeavesFunctionUndeclared)
{
  // SMT-LIB declares no sort named Function, so a script may define one
  reader->set_logic("ALL");
  Sort boolsort = s->make_sort(BOOL);
  reader->define_sort("Function", boolsort);
  EXPECT_EQ(reader->make_sort("Function"), boolsort);
}

TEST_P(Logics, AllAfterTerm)
{
  // a client may make terms of its own before it reads a script in logic
  // ALL, which the native backends accept
  s->make_term(true);
  EXPECT_NO_THROW(reader->set_logic("ALL"));
}

INSTANTIATE_TEST_SUITE_P(
    SmtLibReader,
    Logics,
    testing::ValuesIn(available_non_generic_solver_configurations()),
    ConfigName());

/** Records the values of the set-info commands it reads */
class InfoRecorder : public SmtLibReader
{
 public:
  using SmtLibReader::SmtLibReader;

  void set_info(const string & key, const string & val) override
  {
    info[key] = val;
  }

  unordered_map<string, string> info;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(AttributeValues);
class AttributeValues
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    info = values_in("values.smt2");
  }

  /** The values of the set-info commands of an input from attributes/ */
  unordered_map<string, string> values_in(const string & name)
  {
    InfoRecorder reader(s);
    reader.parse(string(smt_tests::smtlib_resource_dir) + "/attributes/"
                 + name);
    return reader.info;
  }

  SmtSolver s;
  unordered_map<string, string> info;
};

TEST_P(AttributeValues, ListElementsAreSpaced)
{
  EXPECT_EQ(info["list"], "(a (b c) 1 2.5)");
  EXPECT_EQ(info["empty"], "()");
}

TEST_P(AttributeValues, BitVecLiteralsKeepTheirPrefix)
{
  EXPECT_EQ(info["bits"], "#b01");
  EXPECT_EQ(info["hex"], "#x1f");
  EXPECT_EQ(info["bv-list"], "(#b01 #x1f)");
}

TEST_P(AttributeValues, StringsInListsKeepTheirQuotes)
{
  EXPECT_EQ(info["strings"], "(a \"x y\")");
}

TEST_P(AttributeValues, SymbolsInListsKeepNeededBars)
{
  EXPECT_EQ(info["symbols"], "(|a b| c d)");
}

TEST_P(AttributeValues, KeywordsInLists)
{
  EXPECT_EQ(values_in("keyword-in-list.smt2")["keywords"], "(:a b)");
}

TEST_P(AttributeValues, TopLevelStringOrSymbolIsItsText)
{
  EXPECT_EQ(info["string"], "x y");
  EXPECT_EQ(info["symbol"], "a b");
}

TEST_P(AttributeValues, ReservedWordsInLists)
{
  unordered_map<string, string> reserved = values_in("reserved-words.smt2");
  EXPECT_EQ(reserved["set"], "(set-logic set-option set-info)");
  EXPECT_EQ(reserved["declare"], "(declare-const declare-fun declare-sort)");
  EXPECT_EQ(reserved["define"], "(define-fun define-sort)");
  EXPECT_EQ(reserved["check"], "(assert check-sat check-sat-assuming)");
  EXPECT_EQ(reserved["scope"], "(push pop exit)");
  EXPECT_EQ(reserved["get"], "(get-value get-unsat-assumptions echo)");
  EXPECT_EQ(reserved["terms"], "(forall exists let (as const Int))");
  EXPECT_EQ(reserved["indexed"], "((_ bv5 8) (! x :named y))");
}

INSTANTIATE_TEST_SUITE_P(
    SmtLibReader,
    AttributeValues,
    testing::ValuesIn(available_non_generic_solver_configurations()),
    ConfigName());

/** Records the overridable commands it reads that declare, define or
 *  print, each as its name followed by its arguments */
class CommandRecorder : public SmtLibReader
{
 public:
  using SmtLibReader::SmtLibReader;

  void declare_fun(const string & name,
                   SortVec domain,
                   const Sort & sort) override
  {
    vector<string> call = { "declare-fun", name };
    for (const Sort & s : domain)
    {
      call.push_back(to_string(s->get_sort_kind()));
    }
    call.push_back(to_string(sort->get_sort_kind()));
    calls.push_back(call);
  }

  void declare_sort(const string & name, std::uint64_t arity) override
  {
    calls.push_back({ "declare-sort", name, std::to_string(arity) });
  }

  void define_fun(const string & name,
                  const Term & def,
                  const TermVec & args) override
  {
    vector<string> call = { "define-fun", name };
    for (const Term & a : args)
    {
      call.push_back(a->to_string());
    }
    call.push_back(def->to_string());
    calls.push_back(call);
  }

  void define_sort(const string & name, const Sort & sort) override
  {
    calls.push_back({ "define-sort", name, to_string(sort->get_sort_kind()) });
  }

  void get_value(const TermVec & terms) override
  {
    vector<string> call = { "get-value" };
    for (const Term & t : terms)
    {
      call.push_back(t->to_string());
    }
    calls.push_back(call);
  }

  void get_unsat_assumptions() override
  {
    calls.push_back({ "get-unsat-assumptions" });
  }

  void echo(const string & text) override { calls.push_back({ "echo", text }); }

  vector<vector<string>> calls;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Commands);
class Commands : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverConfiguration>
{
};

TEST_P(Commands, OverridesReceiveEachCommand)
{
  SmtSolver s = create_solver(GetParam());
  CommandRecorder reader(s);
  reader.parse(string(smt_tests::smtlib_resource_dir)
               + "/commands/overridable.smt2");
  EXPECT_EQ(reader.calls,
            (vector<vector<string>>{
                { "declare-fun", "f", "BitVec", "BitVec", "BitVec" },
                { "declare-sort", "U", "0" },
                { "define-sort", "T", "BitVec" },
                { "define-fun", "g", "a" },
                { "get-value", "a", "a" },
                { "get-unsat-assumptions" },
                { "echo", "x y" } }));
}

INSTANTIATE_TEST_SUITE_P(
    SmtLibReader,
    Commands,
    testing::ValuesIn(available_non_generic_solver_configurations()),
    ConfigName());

}  // namespace
