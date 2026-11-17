/*!
 * \file ops.cpp
 * \brief All the builtin operators
 * \author Makai Mann
 * \author Clark Barrett
 * \author Áron Ricardo Perez-Lopez
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/ops.h"

#include <algorithm>
#include <climits>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <string>
#include <utility>

#include "smt-switch/exceptions.h"
#include "smt-switch/solver_utils.h"

namespace smt {

namespace {

using Theory = Op::Theory;

/** The SMT-LIB attribute that defines an operator's application to more
 *  than two arguments
 */
enum class Assoc
{
  NONE,
  LEFT,
  RIGHT,
  CHAINABLE,
  PAIRWISE,
};

/** What SMT-LIB defines for an operator */
struct KindInfo
{
  Op::Kind kind;
  const char * name;
  Theory theory;
  std::uint64_t num_indices;
  std::size_t min_arity;
  std::size_t max_arity;
  Assoc assoc;
};

// one row per kind but Op::NONE, in the order of the enum
constexpr KindInfo kind_info[] = {
  { Op::And, "and", Theory::CORE, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::Or, "or", Theory::CORE, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::Xor, "xor", Theory::CORE, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::Not, "not", Theory::CORE, 0, 1, 1, Assoc::NONE },
  { Op::Implies, "=>", Theory::CORE, 0, 2, INT_MAX, Assoc::RIGHT },
  { Op::Ite, "ite", Theory::CORE, 0, 3, 3, Assoc::NONE },
  { Op::Equal, "=", Theory::CORE, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Op::Distinct, "distinct", Theory::CORE, 0, 2, INT_MAX, Assoc::PAIRWISE },
  // at least the function and one argument
  // of course, to be well-sorted the number of arguments must
  // match the function domain
  { Op::Apply, "apply", Theory::UF, 0, 2, INT_MAX, Assoc::NONE },
  { Op::Plus, "+", Theory::ARITH, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::Minus, "-", Theory::ARITH, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::Negate, "-", Theory::ARITH, 0, 1, 1, Assoc::NONE },
  { Op::Mult, "*", Theory::ARITH, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::Div, "/", Theory::REALS, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::Lt, "<", Theory::ARITH, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Op::Le, "<=", Theory::ARITH, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Op::Gt, ">", Theory::ARITH, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Op::Ge, ">=", Theory::ARITH, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Op::Mod, "mod", Theory::INTS, 0, 2, 2, Assoc::NONE },
  { Op::Abs, "abs", Theory::INTS, 0, 1, 1, Assoc::NONE },
  { Op::Pow, "**", Theory::INTS, 0, 2, 2, Assoc::NONE },
  { Op::IntDiv, "div", Theory::INTS, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::Divisible, "divisible", Theory::INTS, 1, 1, 1, Assoc::NONE },
  { Op::To_Real, "to_real", Theory::REALS_INTS, 0, 1, 1, Assoc::NONE },
  { Op::To_Int, "to_int", Theory::REALS_INTS, 0, 1, 1, Assoc::NONE },
  { Op::Is_Int, "is_int", Theory::REALS_INTS, 0, 1, 1, Assoc::NONE },
  { Op::Concat, "concat", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::Extract, "extract", Theory::BITVECTORS, 2, 1, 1, Assoc::NONE },
  { Op::BVNot, "bvnot", Theory::BITVECTORS, 0, 1, 1, Assoc::NONE },
  { Op::BVNeg, "bvneg", Theory::BITVECTORS, 0, 1, 1, Assoc::NONE },
  { Op::BVAnd, "bvand", Theory::BITVECTORS, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::BVOr, "bvor", Theory::BITVECTORS, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::BVXor, "bvxor", Theory::BITVECTORS, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::BVNand, "bvnand", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVNor, "bvnor", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVXnor, "bvxnor", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVAdd, "bvadd", Theory::BITVECTORS, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::BVSub, "bvsub", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVMul, "bvmul", Theory::BITVECTORS, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::BVUdiv, "bvudiv", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVSdiv, "bvsdiv", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVUrem, "bvurem", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVSrem, "bvsrem", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVSmod, "bvsmod", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVShl, "bvshl", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVAshr, "bvashr", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVLshr, "bvlshr", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVComp, "bvcomp", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVUlt, "bvult", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVUle, "bvule", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVUgt, "bvugt", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVUge, "bvuge", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVSlt, "bvslt", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVSle, "bvsle", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVSgt, "bvsgt", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::BVSge, "bvsge", Theory::BITVECTORS, 0, 2, 2, Assoc::NONE },
  { Op::Zero_Extend, "zero_extend", Theory::BITVECTORS, 1, 1, 1, Assoc::NONE },
  { Op::Sign_Extend, "sign_extend", Theory::BITVECTORS, 1, 1, 1, Assoc::NONE },
  { Op::Repeat, "repeat", Theory::BITVECTORS, 1, 1, 1, Assoc::NONE },
  { Op::Rotate_Left, "rotate_left", Theory::BITVECTORS, 1, 1, 1, Assoc::NONE },
  { Op::Rotate_Right,
    "rotate_right",
    Theory::BITVECTORS,
    1,
    1,
    1,
    Assoc::NONE },
  { Op::UBV_To_Int, "ubv_to_int", Theory::BITVECTORS, 0, 1, 1, Assoc::NONE },
  { Op::SBV_To_Int, "sbv_to_int", Theory::BITVECTORS, 0, 1, 1, Assoc::NONE },
  { Op::Int_To_BV, "int_to_bv", Theory::BITVECTORS, 1, 1, 1, Assoc::NONE },
  { Op::StrLt, "str.<", Theory::STRINGS, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Op::StrLeq, "str.<=", Theory::STRINGS, 0, 2, INT_MAX, Assoc::CHAINABLE },
  { Op::StrLen, "str.len", Theory::STRINGS, 0, 1, 1, Assoc::NONE },
  { Op::StrConcat, "str.++", Theory::STRINGS, 0, 2, INT_MAX, Assoc::LEFT },
  { Op::StrSubstr, "str.substr", Theory::STRINGS, 0, 3, 3, Assoc::NONE },
  { Op::StrAt, "str.at", Theory::STRINGS, 0, 2, 2, Assoc::NONE },
  { Op::StrContains, "str.contains", Theory::STRINGS, 0, 2, 2, Assoc::NONE },
  { Op::StrIndexof, "str.indexof", Theory::STRINGS, 0, 3, 3, Assoc::NONE },
  { Op::StrReplace, "str.replace", Theory::STRINGS, 0, 3, 3, Assoc::NONE },
  { Op::StrReplaceAll,
    "str.replace_all",
    Theory::STRINGS,
    0,
    3,
    3,
    Assoc::NONE },
  { Op::StrPrefixof, "str.prefixof", Theory::STRINGS, 0, 2, 2, Assoc::NONE },
  { Op::StrSuffixof, "str.suffixof", Theory::STRINGS, 0, 2, 2, Assoc::NONE },
  { Op::StrIsDigit, "str.is_digit", Theory::STRINGS, 0, 1, 1, Assoc::NONE },
  { Op::Select, "select", Theory::ARRAYS, 0, 2, 2, Assoc::NONE },
  { Op::Store, "store", Theory::ARRAYS, 0, 3, 3, Assoc::NONE },
  // A quantifier binds one parameter, so make_term nests one per parameter;
  // a logging term keeps the parameters as they were given.
  { Op::Forall, "forall", Theory::QUANTIFIERS, 0, 2, 2, Assoc::NONE },
  { Op::Exists, "exists", Theory::QUANTIFIERS, 0, 2, 2, Assoc::NONE },
  { Op::Apply_Selector,
    "apply_selector",
    Theory::DATATYPES,
    0,
    2,
    2,
    Assoc::NONE },
  { Op::Apply_Tester, "apply_tester", Theory::DATATYPES, 0, 2, 2, Assoc::NONE },
  // a nullary constructor is applied to nothing but itself
  { Op::Apply_Constructor,
    "apply_constructor",
    Theory::DATATYPES,
    0,
    1,
    INT_MAX,
    Assoc::NONE },
};

static_assert(std::size(kind_info) == Op::num_kinds - 1,
              "kind_info needs one row per kind but Op::NONE");

constexpr bool rows_follow_enum()
{
  for (std::size_t i = 0; i < std::size(kind_info); ++i)
  {
    if (kind_info[i].kind != static_cast<Op::Kind>(i + 1))
    {
      return false;
    }
  }
  return true;
}
static_assert(rows_follow_enum(),
              "kind_info's rows must be in the order of Op::Kind");

/** The row of kind
 *  @param caller the public function asking, for the message
 *  @throws IncorrectUsageException for Op::NONE or an out-of-range value
 */
const KindInfo & info(Op::Kind kind, const char * caller)
{
  const auto i = static_cast<std::size_t>(kind);
  if (kind == Op::NONE || i >= Op::num_kinds)
  {
    throw IncorrectUsageException(std::string(caller)
                                  + " got a kind that is not an operator: "
                                  + std::to_string(static_cast<int>(kind)));
  }
  return kind_info[i - 1];
}

/** @throws IncorrectUsageException unless kind takes given indices; Op::NONE
 * takes none
 */
void check_num_indices(Op::Kind kind, std::uint64_t given)
{
  const std::uint64_t expected =
      (kind == Op::NONE && given == 0) ? 0 : info(kind, "Op").num_indices;
  if (given != expected)
  {
    throw IncorrectUsageException(to_string(kind) + " takes "
                                  + std::to_string(expected)
                                  + (expected == 1 ? " index" : " indices")
                                  + ", not " + std::to_string(given));
  }
}

}  // namespace

std::string to_string(Op::Kind kind)
{
  if (kind == Op::NONE)
  {
    return "null";
  }
  return info(kind, "to_string").name;
}

std::ostream & operator<<(std::ostream & output, Op::Kind kind)
{
  return output << to_string(kind);
}

Op::Indices::Indices(std::uint64_t index0) : values{ { index0, 0 } }, count(1)
{
}

Op::Indices::Indices(std::uint64_t index0, std::uint64_t index1)
    : values{ { index0, index1 } }, count(2)
{
}

std::size_t Op::Indices::size() const { return count; }

bool Op::Indices::empty() const { return count == 0; }

std::uint64_t Op::Indices::operator[](std::size_t i) const
{
  if (i >= count)
  {
    throw IncorrectUsageException("Op has no index " + std::to_string(i));
  }
  return values[i];
}

const std::uint64_t * Op::Indices::begin() const { return values.data(); }

const std::uint64_t * Op::Indices::end() const { return values.data() + count; }

bool Op::Indices::operator==(const Indices & other) const
{
  return std::equal(begin(), end(), other.begin(), other.end());
}

bool Op::Indices::operator!=(const Indices & other) const
{
  return !(*this == other);
}

Op::Op(Kind kind) : kind_(kind) { check_num_indices(kind, 0); }

Op::Op(Kind kind, std::uint64_t index0) : indices(index0), kind_(kind)
{
  check_num_indices(kind, 1);
}

Op::Op(Kind kind, std::uint64_t index0, std::uint64_t index1)
    : indices(index0, index1), kind_(kind)
{
  check_num_indices(kind, 2);
}

Op::Kind Op::kind() const { return kind_; }

std::pair<std::size_t, std::size_t> Op::arity() const
{
  const KindInfo & row = info(kind_, "Op::arity");
  return { row.min_arity, row.max_arity };
}

Op::Theory Op::theory() const { return info(kind_, "Op::theory").theory; }

bool Op::is_null() const { return kind_ == NONE; }

bool Op::is_apply() const
{
  return kind_ == Apply || kind_ == Apply_Constructor || kind_ == Apply_Selector
         || kind_ == Apply_Tester;
}

bool Op::is_left_assoc() const
{
  return info(kind_, "Op::is_left_assoc").assoc == Assoc::LEFT;
}

bool Op::is_right_assoc() const
{
  return info(kind_, "Op::is_right_assoc").assoc == Assoc::RIGHT;
}

bool Op::is_chainable() const
{
  return info(kind_, "Op::is_chainable").assoc == Assoc::CHAINABLE;
}

bool Op::is_pairwise() const
{
  return info(kind_, "Op::is_pairwise").assoc == Assoc::PAIRWISE;
}

bool Op::is_variadic() const
{
  return info(kind_, "Op::is_variadic").assoc != Assoc::NONE;
}

std::string Op::to_string() const
{
  if (indices.empty())
  {
    return smt::to_string(kind_);
  }

  std::string res = "(_ " + smt::to_string(kind_);
  for (const auto index : indices)
  {
    res += " " + std::to_string(index);
  }
  res += ")";
  return res;
}

bool operator==(Op o1, Op o2)
{
  return o1.kind() == o2.kind() && o1.indices == o2.indices;
}

bool operator!=(Op o1, Op o2) { return !(o1 == o2); }

std::ostream & operator<<(std::ostream & output, const Op o)
{
  output << o.to_string();
  return output;
}

}  // namespace smt

namespace std {

size_t hash<smt::Op>::operator()(const smt::Op o) const
{
  // the kind and the indices, which == compares
  size_t h = hash<smt::Op::Kind>{}(o.kind());
  for (uint64_t index : o.indices)
  {
    smt::backend::hash_combine(h, index);
  }
  return h;
}

}  // namespace std
