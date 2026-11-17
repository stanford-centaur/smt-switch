/*!
 * \file cvc5_term.cpp
 * \brief cvc5 implementation of AbsTerm
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/cvc5_term.h"

#include <cvc5/cvc5.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <memory>
#include <string>
#include <utility>

#include "smt-switch/cvc5_sort.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/solver_utils.h"
#include "smt-switch/text_utils.h"

namespace smt {

namespace {

// Each operator with the cvc5 kind of its applications, a row per kind but
// Op::NONE in the order of the enum, then the kinds only ever looked up from
// the cvc5 kind
//
// Both lookups index an array rather than search this table. get_op runs
// for every node a traversal visits, and a linear search made it about a
// third slower than the hash map these replace.
constexpr std::pair<Op::Kind, cvc5::Kind> kind_pairs[] = {
  { Op::And, cvc5::Kind::AND },
  { Op::Or, cvc5::Kind::OR },
  { Op::Xor, cvc5::Kind::XOR },
  { Op::Not, cvc5::Kind::NOT },
  { Op::Implies, cvc5::Kind::IMPLIES },
  { Op::Ite, cvc5::Kind::ITE },
  { Op::Equal, cvc5::Kind::EQUAL },
  { Op::Distinct, cvc5::Kind::DISTINCT },
  { Op::Apply, cvc5::Kind::APPLY_UF },
  { Op::Plus, cvc5::Kind::ADD },
  { Op::Minus, cvc5::Kind::SUB },
  { Op::Negate, cvc5::Kind::NEG },
  { Op::Mult, cvc5::Kind::MULT },
  { Op::Div, cvc5::Kind::DIVISION },
  { Op::Lt, cvc5::Kind::LT },
  { Op::Le, cvc5::Kind::LEQ },
  { Op::Gt, cvc5::Kind::GT },
  { Op::Ge, cvc5::Kind::GEQ },
  { Op::Mod, cvc5::Kind::INTS_MODULUS },
  { Op::Abs, cvc5::Kind::ABS },
  { Op::Pow, cvc5::Kind::POW },
  { Op::IntDiv, cvc5::Kind::INTS_DIVISION },
  { Op::Divisible, cvc5::Kind::DIVISIBLE },
  { Op::To_Real, cvc5::Kind::TO_REAL },
  { Op::To_Int, cvc5::Kind::TO_INTEGER },
  { Op::Is_Int, cvc5::Kind::IS_INTEGER },
  { Op::Concat, cvc5::Kind::BITVECTOR_CONCAT },
  { Op::Extract, cvc5::Kind::BITVECTOR_EXTRACT },
  { Op::BVNot, cvc5::Kind::BITVECTOR_NOT },
  { Op::BVNeg, cvc5::Kind::BITVECTOR_NEG },
  { Op::BVAnd, cvc5::Kind::BITVECTOR_AND },
  { Op::BVOr, cvc5::Kind::BITVECTOR_OR },
  { Op::BVXor, cvc5::Kind::BITVECTOR_XOR },
  { Op::BVNand, cvc5::Kind::BITVECTOR_NAND },
  { Op::BVNor, cvc5::Kind::BITVECTOR_NOR },
  { Op::BVXnor, cvc5::Kind::BITVECTOR_XNOR },
  { Op::BVAdd, cvc5::Kind::BITVECTOR_ADD },
  { Op::BVSub, cvc5::Kind::BITVECTOR_SUB },
  { Op::BVMul, cvc5::Kind::BITVECTOR_MULT },
  { Op::BVUdiv, cvc5::Kind::BITVECTOR_UDIV },
  { Op::BVSdiv, cvc5::Kind::BITVECTOR_SDIV },
  { Op::BVUrem, cvc5::Kind::BITVECTOR_UREM },
  { Op::BVSrem, cvc5::Kind::BITVECTOR_SREM },
  { Op::BVSmod, cvc5::Kind::BITVECTOR_SMOD },
  { Op::BVShl, cvc5::Kind::BITVECTOR_SHL },
  { Op::BVAshr, cvc5::Kind::BITVECTOR_ASHR },
  { Op::BVLshr, cvc5::Kind::BITVECTOR_LSHR },
  { Op::BVComp, cvc5::Kind::BITVECTOR_COMP },
  { Op::BVUlt, cvc5::Kind::BITVECTOR_ULT },
  { Op::BVUle, cvc5::Kind::BITVECTOR_ULE },
  { Op::BVUgt, cvc5::Kind::BITVECTOR_UGT },
  { Op::BVUge, cvc5::Kind::BITVECTOR_UGE },
  { Op::BVSlt, cvc5::Kind::BITVECTOR_SLT },
  { Op::BVSle, cvc5::Kind::BITVECTOR_SLE },
  { Op::BVSgt, cvc5::Kind::BITVECTOR_SGT },
  { Op::BVSge, cvc5::Kind::BITVECTOR_SGE },
  { Op::Zero_Extend, cvc5::Kind::BITVECTOR_ZERO_EXTEND },
  { Op::Sign_Extend, cvc5::Kind::BITVECTOR_SIGN_EXTEND },
  { Op::Repeat, cvc5::Kind::BITVECTOR_REPEAT },
  { Op::Rotate_Left, cvc5::Kind::BITVECTOR_ROTATE_LEFT },
  { Op::Rotate_Right, cvc5::Kind::BITVECTOR_ROTATE_RIGHT },
  { Op::UBV_To_Int, cvc5::Kind::BITVECTOR_UBV_TO_INT },
  { Op::SBV_To_Int, cvc5::Kind::BITVECTOR_SBV_TO_INT },
  { Op::Int_To_BV, cvc5::Kind::INT_TO_BITVECTOR },
  { Op::StrLt, cvc5::Kind::STRING_LT },
  { Op::StrLeq, cvc5::Kind::STRING_LEQ },
  { Op::StrLen, cvc5::Kind::STRING_LENGTH },
  { Op::StrConcat, cvc5::Kind::STRING_CONCAT },
  { Op::StrSubstr, cvc5::Kind::STRING_SUBSTR },
  { Op::StrAt, cvc5::Kind::STRING_CHARAT },
  { Op::StrContains, cvc5::Kind::STRING_CONTAINS },
  { Op::StrIndexof, cvc5::Kind::STRING_INDEXOF },
  { Op::StrReplace, cvc5::Kind::STRING_REPLACE },
  { Op::StrReplaceAll, cvc5::Kind::STRING_REPLACE_ALL },
  { Op::StrPrefixof, cvc5::Kind::STRING_PREFIX },
  { Op::StrSuffixof, cvc5::Kind::STRING_SUFFIX },
  { Op::StrIsDigit, cvc5::Kind::STRING_IS_DIGIT },
  { Op::Select, cvc5::Kind::SELECT },
  { Op::Store, cvc5::Kind::STORE },
  { Op::Forall, cvc5::Kind::FORALL },
  { Op::Exists, cvc5::Kind::EXISTS },
  { Op::Apply_Selector, cvc5::Kind::APPLY_SELECTOR },
  { Op::Apply_Tester, cvc5::Kind::APPLY_TESTER },
  { Op::Apply_Constructor, cvc5::Kind::APPLY_CONSTRUCTOR },
  // The deprecated cvc5 kind for UBV_To_Int, only ever looked up from the kind
  { Op::UBV_To_Int, cvc5::Kind::BITVECTOR_TO_NAT },
};

constexpr bool rows_follow_enum()
{
  for (std::size_t i = 0; i < Op::num_kinds - 1; ++i)
  {
    if (kind_pairs[i].first != static_cast<Op::Kind>(i + 1))
    {
      return false;
    }
  }
  return true;
}
static_assert(std::size(kind_pairs) >= Op::num_kinds - 1 && rows_follow_enum(),
              "kind_pairs needs a row per kind but Op::NONE, in the order "
              "of the enum");

// The cvc5 kinds, from INTERNAL_KIND up to LAST_KIND, as array indices
constexpr int first_kind = static_cast<int>(cvc5::Kind::INTERNAL_KIND);
constexpr std::size_t num_kinds =
    static_cast<int>(cvc5::Kind::LAST_KIND) - first_kind;

// The operator of each cvc5 kind, from the last row that has it, or
// Op::NONE for a kind that no operator stands for
struct OpKindTable
{
  constexpr OpKindTable()
  {
    for (const std::pair<Op::Kind, cvc5::Kind> & row : kind_pairs)
    {
      op_kinds[static_cast<std::size_t>(static_cast<int>(row.second)
                                        - first_kind)] = row.first;
    }
  }
  std::array<Op::Kind, num_kinds> op_kinds = {};
};
constexpr OpKindTable op_kind_table;

// Whether a cvc5 term is a literal, an abstract value, a constructor
// applied to values or a store of values
bool is_cvc5_value(const cvc5::Term & term)
{
  cvc5::Kind k = term.getKind();
  if (k == cvc5::Kind::APPLY_CONSTRUCTOR)
  {
    // The first child is the constructor itself.
    for (std::size_t i = 1; i < term.getNumChildren(); ++i)
    {
      if (!is_cvc5_value(term[i]))
      {
        return false;
      }
    }
    return true;
  }
  if (k == cvc5::Kind::STORE)
  {
    // SMT-LIB's ArraysEx makes a store of a value into an array value a value
    for (std::size_t i = 0; i < term.getNumChildren(); ++i)
    {
      if (!is_cvc5_value(term[i]))
      {
        return false;
      }
    }
    return true;
  }
  // checking all possible const types for future-proofing
  // not all these sorts are even supported at this time
  return k == cvc5::Kind::UNINTERPRETED_SORT_VALUE
         || k == cvc5::Kind::CONST_BOOLEAN || k == cvc5::Kind::CONST_RATIONAL
         || k == cvc5::Kind::CONST_INTEGER || k == cvc5::Kind::CONST_BITVECTOR
         || k == cvc5::Kind::CONST_FINITE_FIELD
         || k == cvc5::Kind::CONST_FLOATINGPOINT
         || k == cvc5::Kind::CONST_ROUNDINGMODE || k == cvc5::Kind::CONST_ARRAY
         || k == cvc5::Kind::CONST_STRING || k == cvc5::Kind::CONST_SEQUENCE;
}

/** Index i of an indexed cvc5 op, which an smt-switch Op holds only if it
 *  is a natural number that fits in 64 bits
 */
std::uint64_t op_index(cvc5::Op op, std::size_t i)
{
  const cvc5::Term index = op[i];
  if (!index.isUInt64Value())
  {
    throw NotImplementedException("smt-switch has no op for the cvc5 op "
                                  + op.toString());
  }
  return index.getUInt64Value();
}

// struct for hashing
std::hash<cvc5::Term> termhash;

/** The operator of the applications of kind
 *  @throws NotImplementedException for a kind that no operator stands for
 */
Op::Kind to_op_kind(cvc5::Kind kind)
{
  const int i = static_cast<int>(kind) - first_kind;
  if (i < 0 || static_cast<std::size_t>(i) >= num_kinds
      || op_kind_table.op_kinds[i] == Op::NONE)
  {
    throw NotImplementedException(
        "smt-switch has no operator for the cvc5 Kind " + std::to_string(kind));
  }
  return op_kind_table.op_kinds[i];
}

/** The cvc5 kind of the applications of k
 *  @throws IncorrectUsageException for Op::NONE or an out-of-range value
 */
cvc5::Kind to_cvc5_kind(Op::Kind k)
{
  if (k == Op::NONE || k >= Op::num_kinds)
  {
    throw IncorrectUsageException("cvc5 has no kind for the operator kind "
                                  + std::to_string(static_cast<int>(k)));
  }
  return kind_pairs[k - 1].second;
}

/** The application of op to children, made by tm. A quantifier binds its
 *  parameters one at a time, which makes traversal easier since smt-switch
 *  has no VARIABLE_LIST equivalent.
 */
cvc5::Term make_application(cvc5::TermManager & tm,
                            const Op & op,
                            std::vector<cvc5::Term> children)
{
  const cvc5::Kind kind = to_cvc5_kind(op.kind());
  if (op.kind() == Op::Forall || op.kind() == Op::Exists)
  {
    cvc5::Term res = children.back();
    children.pop_back();
    while (!children.empty())
    {
      cvc5::Term bound_var =
          tm.mkTerm(cvc5::Kind::VARIABLE_LIST, { children.back() });
      children.pop_back();
      res = tm.mkTerm(kind, { bound_var, res });
    }
    return res;
  }
  if (op.indices.empty())
  {
    return tm.mkTerm(kind, children);
  }
  std::vector<std::uint32_t> indices;
  for (std::uint64_t index : op.indices)
  {
    indices.push_back(backend::narrow_index(op, index));
  }
  return tm.mkTerm(tm.mkOp(kind, indices), children);
}

}  // namespace

/* Cvc5Term implementation */

Cvc5Term::Cvc5Term(cvc5::Term t) : term(t) {}

Cvc5Term::Cvc5Term(cvc5::TermManager & tm,
                   const Op & op,
                   const std::vector<cvc5::Term> & children)
    : term(make_application(tm, op, children))
{
}

std::size_t Cvc5Term::hash() const { return termhash(term); }

std::size_t Cvc5Term::get_id() const { return term.getId(); }

bool Cvc5Term::compare(const Term & absterm) const
{
  std::shared_ptr<Cvc5Term> other =
      std::dynamic_pointer_cast<Cvc5Term>(absterm);
  return other && term == other->term;
}

Op Cvc5Term::get_op() const
{
  if (!term.hasOp())
  {
    // Return a null op.
    return Op();
  }

  cvc5::Op cvc5_op = term.getOp();
  cvc5::Kind cvc5_kind = cvc5_op.getKind();

  // Special cases
  if (cvc5_kind == cvc5::Kind::CONST_ARRAY)
  {
    // A constant array is a value in smt-switch.
    return Op();
  }

  const auto op_kind = to_op_kind(cvc5_kind);
  const auto num_indices = cvc5_op.getNumIndices();
  // Op refuses a number of indices its kind does not take
  try
  {
    if (!cvc5_op.isIndexed())
    {
      return Op(op_kind);
    }
    if (num_indices == 1)
    {
      return Op(op_kind, op_index(cvc5_op, 0));
    }
    if (num_indices == 2)
    {
      return Op(op_kind, op_index(cvc5_op, 0), op_index(cvc5_op, 1));
    }
  }
  catch (const IncorrectUsageException &)
  {
  }
  throw NotImplementedException("smt-switch has no operator for the cvc5 Kind "
                                + std::to_string(cvc5_kind) + " with "
                                + std::to_string(num_indices)
                                + (num_indices == 1 ? " index" : " indices"));
}

Sort Cvc5Term::get_sort() const
{
  return std::make_shared<Cvc5Sort>(term.getSort());
}

bool Cvc5Term::is_symbol() const
{
  // functions, parameters, and symbolic constants are all symbols
  cvc5::Kind k = term.getKind();
  return (k == cvc5::Kind::CONSTANT || k == cvc5::Kind::VARIABLE);
}

bool Cvc5Term::is_param() const
{
  return (term.getKind() == cvc5::Kind::VARIABLE);
}

bool Cvc5Term::is_symbolic_const() const
{
  return (term.getKind() == cvc5::Kind::CONSTANT
          && !term.getSort().isFunction());
}

bool Cvc5Term::is_value() const { return is_cvc5_value(term); }

std::string Cvc5Term::to_string() const
{
  // cvc5 prints a tester by an internal name of its own, is_C, which is no
  // SMT-LIB term
  if (term.getSort().isDatatypeTester())
  {
    return "(_ is " + smtlib::quote_symbol(get_constructor_name()) + ")";
  }
  return term.toString();
}

std::wstring Cvc5Term::getStringValue() const
{
  const std::u32string value = term.getU32StringValue();
  return std::wstring(value.begin(), value.end());
}

std::string Cvc5Term::get_constructor_name() const
{
  // a constructor or tester is found among its datatype's
  cvc5::Sort sort = term.getSort();
  if (sort.isDatatypeConstructor())
  {
    cvc5::Datatype dt = sort.getDatatypeConstructorCodomainSort().getDatatype();
    for (std::size_t i = 0; i != dt.getNumConstructors(); i++)
    {
      if (dt[i].getTerm() == term)
      {
        return dt[i].getName();
      }
    }
  }
  if (sort.isDatatypeTester())
  {
    cvc5::Datatype dt = sort.getDatatypeTesterDomainSort().getDatatype();
    for (std::size_t i = 0; i != dt.getNumConstructors(); i++)
    {
      if (dt[i].getTesterTerm() == term)
      {
        return dt[i].getName();
      }
    }
  }
  throw IncorrectUsageException(
      "Only a constructor or a tester has a constructor name");
}

std::string Cvc5Term::get_param_name() const
{
  if (!is_param())
  {
    throw IncorrectUsageException("Only a param has a param name");
  }
  return term.getSymbol();
}

std::string Cvc5Term::get_selector_name() const
{
  // a selector is found among its datatype's
  cvc5::Sort sort = term.getSort();
  if (sort.isDatatypeSelector())
  {
    cvc5::Datatype dt = sort.getDatatypeSelectorDomainSort().getDatatype();
    for (std::size_t i = 0; i != dt.getNumConstructors(); i++)
    {
      for (std::size_t j = 0; j != dt[i].getNumSelectors(); j++)
      {
        if (dt[i][j].getTerm() == term)
        {
          return dt[i][j].getName();
        }
      }
    }
  }
  throw IncorrectUsageException("Only a selector has a selector name");
}

std::string Cvc5Term::get_symbol_name() const
{
  if (term.getKind() != cvc5::Kind::CONSTANT)
  {
    throw IncorrectUsageException(
        "Only a symbol that is not a param has a symbol name");
  }
  return term.getSymbol();
}

uint64_t Cvc5Term::to_int() const
{
  if (term.isBitVectorValue())
  {
    return bits_to_uint64(to_bits());
  }
  // true for integer values and for real values with an integral value
  if (term.isUInt64Value())
  {
    return term.getUInt64Value();
  }
  throw IncorrectUsageException(
      "Can't convert " + term.toString()
      + " to an unsigned integer: it is not a value that fits in 64 bits");
}

int64_t Cvc5Term::to_signed_int() const
{
  if (term.isBitVectorValue())
  {
    return bits_to_int64(to_bits());
  }
  // true for integer values and for real values with an integral value
  if (term.isInt64Value())
  {
    return term.getInt64Value();
  }
  throw IncorrectUsageException(
      "Can't convert " + term.toString()
      + " to a signed integer: it is not a value that fits in 64 bits");
}

std::string Cvc5Term::to_bits() const
{
  if (!term.isBitVectorValue())
  {
    throw IncorrectUsageException(
        "Can't get a bitstring from a term that is not a bit-vector value");
  }
  return term.getBitVectorValue(2);
}

bool Cvc5Term::to_bool() const
{
  if (!term.isBooleanValue())
  {
    throw IncorrectUsageException("Can't convert " + term.toString()
                                  + " to a Boolean: it is not a Boolean value");
  }
  return term.getBooleanValue();
}

// The children smt-switch lists: cvc5's, then a constant array's base
std::size_t Cvc5Term::get_num_children() const
{
  std::size_t n = term.getNumChildren();
  return term.getKind() == cvc5::Kind::CONST_ARRAY ? n + 1 : n;
}

Term Cvc5Term::get_child(std::size_t i) const
{
  if (i == term.getNumChildren() && term.getKind() == cvc5::Kind::CONST_ARRAY)
  {
    return std::make_shared<Cvc5Term>(term.getConstArrayBase());
  }
  // special-case for VARIABLE_LIST -- parameters bound by a quantifier
  // smt-switch cvc5 backend guarantees that the length is only one by
  // construction
  cvc5::Term t = term[i];
  if (t.getKind() == cvc5::Kind::VARIABLE_LIST)
  {
    if (t.getNumChildren() != 1)
    {
      // smt-switch cvc5 backend should only allow binding one parameter
      // otherwise, we need to flatten arbitrary nestings of quantifiers and
      // VARIABLE_LISTs for term iteration
      throw SolverException(
          "Expected exactly one bound variable in cvc5 VARIABLE_LIST");
    }
    return std::make_shared<Cvc5Term>(t[0]);
  }
  return std::make_shared<Cvc5Term>(t);
}

std::string Cvc5Term::print_value_as(SortKind /* sk */) const
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Can't use print_value_as on a term that is not a value");
  }
  return term.toString();
}

cvc5::Term Cvc5Term::get_cvc5_term() const { return term; }

/* end Cvc5Term implementation */

}  // namespace smt
