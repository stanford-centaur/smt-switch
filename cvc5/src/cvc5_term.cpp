/*********************                                                        */
/*! \file cvc5_term.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief cvc5 implementation of AbsTerm
**
**
**/

#include "cvc5_term.h"

#include <cvc5/cvc5.h>

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <memory>
#include <string>
#include <utility>

#include "cvc5_sort.h"
#include "exceptions.h"
#include "ops.h"
#include "solver_utils.h"
#include "utils.h"

namespace smt {

namespace {

// Each PrimOp with the cvc5 kind of its applications, a row per PrimOp in
// the order of the enum, then the kinds only ever looked up from the kind
//
// Both lookups index an array rather than search this table. get_op runs
// for every node a traversal visits, and a linear search made it about a
// third slower than the hash map these replace.
constexpr std::pair<PrimOp, cvc5::Kind> primop_kinds[] = {
  { And, cvc5::Kind::AND },
  { Or, cvc5::Kind::OR },
  { Xor, cvc5::Kind::XOR },
  { Not, cvc5::Kind::NOT },
  { Implies, cvc5::Kind::IMPLIES },
  { Ite, cvc5::Kind::ITE },
  { Equal, cvc5::Kind::EQUAL },
  { Distinct, cvc5::Kind::DISTINCT },
  { Apply, cvc5::Kind::APPLY_UF },
  { Plus, cvc5::Kind::ADD },
  { Minus, cvc5::Kind::SUB },
  { Negate, cvc5::Kind::NEG },
  { Mult, cvc5::Kind::MULT },
  { Div, cvc5::Kind::DIVISION },
  { Lt, cvc5::Kind::LT },
  { Le, cvc5::Kind::LEQ },
  { Gt, cvc5::Kind::GT },
  { Ge, cvc5::Kind::GEQ },
  { Mod, cvc5::Kind::INTS_MODULUS },
  { Abs, cvc5::Kind::ABS },
  { Pow, cvc5::Kind::POW },
  { IntDiv, cvc5::Kind::INTS_DIVISION },
  { To_Real, cvc5::Kind::TO_REAL },
  { To_Int, cvc5::Kind::TO_INTEGER },
  { Is_Int, cvc5::Kind::IS_INTEGER },
  { Concat, cvc5::Kind::BITVECTOR_CONCAT },
  { Extract, cvc5::Kind::BITVECTOR_EXTRACT },
  { BVNot, cvc5::Kind::BITVECTOR_NOT },
  { BVNeg, cvc5::Kind::BITVECTOR_NEG },
  { BVAnd, cvc5::Kind::BITVECTOR_AND },
  { BVOr, cvc5::Kind::BITVECTOR_OR },
  { BVXor, cvc5::Kind::BITVECTOR_XOR },
  { BVNand, cvc5::Kind::BITVECTOR_NAND },
  { BVNor, cvc5::Kind::BITVECTOR_NOR },
  { BVXnor, cvc5::Kind::BITVECTOR_XNOR },
  { BVAdd, cvc5::Kind::BITVECTOR_ADD },
  { BVSub, cvc5::Kind::BITVECTOR_SUB },
  { BVMul, cvc5::Kind::BITVECTOR_MULT },
  { BVUdiv, cvc5::Kind::BITVECTOR_UDIV },
  { BVSdiv, cvc5::Kind::BITVECTOR_SDIV },
  { BVUrem, cvc5::Kind::BITVECTOR_UREM },
  { BVSrem, cvc5::Kind::BITVECTOR_SREM },
  { BVSmod, cvc5::Kind::BITVECTOR_SMOD },
  { BVShl, cvc5::Kind::BITVECTOR_SHL },
  { BVAshr, cvc5::Kind::BITVECTOR_ASHR },
  { BVLshr, cvc5::Kind::BITVECTOR_LSHR },
  { BVComp, cvc5::Kind::BITVECTOR_COMP },
  { BVUlt, cvc5::Kind::BITVECTOR_ULT },
  { BVUle, cvc5::Kind::BITVECTOR_ULE },
  { BVUgt, cvc5::Kind::BITVECTOR_UGT },
  { BVUge, cvc5::Kind::BITVECTOR_UGE },
  { BVSlt, cvc5::Kind::BITVECTOR_SLT },
  { BVSle, cvc5::Kind::BITVECTOR_SLE },
  { BVSgt, cvc5::Kind::BITVECTOR_SGT },
  { BVSge, cvc5::Kind::BITVECTOR_SGE },
  { Zero_Extend, cvc5::Kind::BITVECTOR_ZERO_EXTEND },
  { Sign_Extend, cvc5::Kind::BITVECTOR_SIGN_EXTEND },
  { Repeat, cvc5::Kind::BITVECTOR_REPEAT },
  { Rotate_Left, cvc5::Kind::BITVECTOR_ROTATE_LEFT },
  { Rotate_Right, cvc5::Kind::BITVECTOR_ROTATE_RIGHT },
  { BV_To_Nat, cvc5::Kind::BITVECTOR_UBV_TO_INT },
  { UBV_To_Int, cvc5::Kind::BITVECTOR_UBV_TO_INT },
  { SBV_To_Int, cvc5::Kind::BITVECTOR_SBV_TO_INT },
  { Int_To_BV, cvc5::Kind::INT_TO_BITVECTOR },
  { StrLt, cvc5::Kind::STRING_LT },
  { StrLeq, cvc5::Kind::STRING_LEQ },
  { StrLen, cvc5::Kind::STRING_LENGTH },
  { StrConcat, cvc5::Kind::STRING_CONCAT },
  { StrSubstr, cvc5::Kind::STRING_SUBSTR },
  { StrAt, cvc5::Kind::STRING_CHARAT },
  { StrContains, cvc5::Kind::STRING_CONTAINS },
  { StrIndexof, cvc5::Kind::STRING_INDEXOF },
  { StrReplace, cvc5::Kind::STRING_REPLACE },
  { StrReplaceAll, cvc5::Kind::STRING_REPLACE_ALL },
  { StrPrefixof, cvc5::Kind::STRING_PREFIX },
  { StrSuffixof, cvc5::Kind::STRING_SUFFIX },
  { StrIsDigit, cvc5::Kind::STRING_IS_DIGIT },
  { Select, cvc5::Kind::SELECT },
  { Store, cvc5::Kind::STORE },
  { Forall, cvc5::Kind::FORALL },
  { Exists, cvc5::Kind::EXISTS },
  { Apply_Selector, cvc5::Kind::APPLY_SELECTOR },
  { Apply_Tester, cvc5::Kind::APPLY_TESTER },
  { Apply_Constructor, cvc5::Kind::APPLY_CONSTRUCTOR },
  // The deprecated cvc5 kind for UBV_To_Int, only ever looked up from the kind
  { UBV_To_Int, cvc5::Kind::BITVECTOR_TO_NAT },
};

constexpr bool rows_follow_enum()
{
  for (std::size_t i = 0; i < NUM_OPS_AND_NULL; ++i)
  {
    if (primop_kinds[i].first != static_cast<PrimOp>(i))
    {
      return false;
    }
  }
  return true;
}
static_assert(std::size(primop_kinds) >= NUM_OPS_AND_NULL && rows_follow_enum(),
              "primop_kinds needs a row per PrimOp, in the order of the enum");

// The cvc5 kinds, from INTERNAL_KIND up to LAST_KIND, as array indices
constexpr int first_kind = static_cast<int>(cvc5::Kind::INTERNAL_KIND);
constexpr std::size_t num_kinds =
    static_cast<int>(cvc5::Kind::LAST_KIND) - first_kind;

// The PrimOp of each cvc5 kind, from the last row that has it, or
// NUM_OPS_AND_NULL for a kind that no PrimOp stands for
struct KindPrimops
{
  constexpr KindPrimops() : primops{}
  {
    for (PrimOp & po : primops)
    {
      po = NUM_OPS_AND_NULL;
    }
    for (const std::pair<PrimOp, cvc5::Kind> & row : primop_kinds)
    {
      primops[static_cast<std::size_t>(static_cast<int>(row.second)
                                       - first_kind)] = row.first;
    }
  }
  std::array<PrimOp, num_kinds> primops;
};
constexpr KindPrimops kind_primops;

}  // namespace

cvc5::Kind to_cvc5_kind(PrimOp po)
{
  if (po >= NUM_OPS_AND_NULL)
  {
    throw IncorrectUsageException("cvc5 has no kind for the PrimOp "
                                  + std::to_string(static_cast<int>(po)));
  }
  return primop_kinds[po].second;
}

PrimOp to_primop(cvc5::Kind kind)
{
  const int i = static_cast<int>(kind) - first_kind;
  if (i < 0 || static_cast<std::size_t>(i) >= num_kinds
      || kind_primops.primops[i] == NUM_OPS_AND_NULL)
  {
    throw NotImplementedException("smt-switch has no PrimOp for the cvc5 Kind "
                                  + std::to_string(kind));
  }
  return kind_primops.primops[i];
}

// struct for hashing
std::hash<cvc5::Term> termhash;

/* Cvc5TermIter implementation */
Cvc5TermIter::Cvc5TermIter(::cvc5::Term t, uint32_t p) : term(t), pos(p) {}

void Cvc5TermIter::operator++() { pos++; }

Term Cvc5TermIter::operator*() const
{
  if (pos == term.getNumChildren()
      && term.getKind() == ::cvc5::Kind::CONST_ARRAY)
  {
    return std::make_shared<Cvc5Term>(term.getConstArrayBase());
  }
  // special-case for VARIABLE_LIST -- parameters bound by a quantifier
  // smt-switch cvc5 backend guarantees that the length is only one by
  // construction
  ::cvc5::Term t = term[pos];
  if (t.getKind() == ::cvc5::Kind::VARIABLE_LIST)
  {
    if (t.getNumChildren() != 1)
    {
      // smt-switch cvc5 backend should only allow binding one parameter
      // otherwise, we need to flatten arbitrary nestings of quantifiers and
      // VARIABLE_LISTs for term iteration
      throw InternalSolverException(
          "Expected exactly one bound variable in cvc5 VARIABLE_LIST");
    }
    return std::make_shared<Cvc5Term>(t[0]);
  }
  return std::make_shared<Cvc5Term>(t);
}

TermIterBase * Cvc5TermIter::clone() const
{
  return new Cvc5TermIter(term, pos);
}

bool Cvc5TermIter::operator==(const Cvc5TermIter & it) const
{
  return term == it.term && pos == it.pos;
}

bool Cvc5TermIter::operator!=(const Cvc5TermIter & it) const
{
  return term != it.term || pos != it.pos;
}

bool Cvc5TermIter::equal(const TermIterBase & other) const
{
  const Cvc5TermIter & cti = static_cast<const Cvc5TermIter &>(other);
  return term == cti.term && pos == cti.pos;
}

/* end Cvc5TermIter implementation */

/* Cvc5Term implementation */

Cvc5Term::Cvc5Term(cvc5::Term t) : term(t) {}

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

  const PrimOp po = to_primop(cvc5_kind);

  // Create an smt-switch Op and return it.
  if (cvc5_op.isIndexed())
  {
    const std::uint64_t num_indices = get_num_indices(po);
    if (num_indices == 0)
    {
      throw NotImplementedException("get_op not implemented for cvc5 Kind "
                                    + std::to_string(cvc5_kind));
    }
    if (num_indices == 1)
    {
      uint64_t idx0 = std::stoull(cvc5_op[0].toString());
      return Op(po, idx0);
    }
    else
    {
      assert(num_indices == 2);
      std::pair<uint64_t, uint64_t> indices = {
        std::stoull(cvc5_op[0].toString()), std::stoull(cvc5_op[1].toString())
      };
      return Op(po, indices.first, indices.second);
    }
  }
  else
  {
    return Op(po);
  }
}

Sort Cvc5Term::get_sort() const
{
  return std::make_shared<Cvc5Sort>(term.getSort());
}

bool Cvc5Term::is_symbol() const
{
  // functions, parameters, and symbolic constants are all symbols
  ::cvc5::Kind k = term.getKind();
  return (k == ::cvc5::Kind::CONSTANT || k == ::cvc5::Kind::VARIABLE);
}

bool Cvc5Term::is_param() const
{
  return (term.getKind() == ::cvc5::Kind::VARIABLE);
}

bool Cvc5Term::is_symbolic_const() const
{
  return (term.getKind() == ::cvc5::Kind::CONSTANT
          && !term.getSort().isFunction());
}

bool Cvc5Term::is_value() const
{
  // checking all possible const types for future-proofing
  // not all these sorts are even supported at this time
  ::cvc5::Kind k = term.getKind();
  return ((k == ::cvc5::Kind::CONST_BOOLEAN)
          || (k == ::cvc5::Kind::CONST_BITVECTOR)
          || (k == ::cvc5::Kind::CONST_RATIONAL)
          || (k == ::cvc5::Kind::CONST_INTEGER)
          || (k == ::cvc5::Kind::CONST_FINITE_FIELD)
          || (k == ::cvc5::Kind::CONST_FLOATINGPOINT)
          || (k == ::cvc5::Kind::CONST_ROUNDINGMODE)
          || (k == ::cvc5::Kind::CONST_STRING)
          || (k == ::cvc5::Kind::CONST_SEQUENCE)
          || (k == ::cvc5::Kind::CONST_ARRAY));
}

std::string Cvc5Term::to_string() const { return term.toString(); }

std::wstring Cvc5Term::getStringValue() const
{
  const std::u32string value = term.getU32StringValue();
  return std::wstring(value.begin(), value.end());
}

uint64_t Cvc5Term::to_int() const
{
  if (term.isBitVectorValue())
  {
    return bits_to_uint64(term.getBitVectorValue(2));
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
    return bits_to_int64(term.getBitVectorValue(2));
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

/** Iterators for traversing the children
 */
TermIter Cvc5Term::begin() const { return TermIter(new Cvc5TermIter(term, 0)); }

TermIter Cvc5Term::end() const
{
  uint32_t num_children =
      detail::narrow<uint32_t>(term.getNumChildren(), "a number of children");
  if (term.getKind() == ::cvc5::Kind::CONST_ARRAY)
  {
    // base of constant array is the child
    num_children++;
  }
  return TermIter(new Cvc5TermIter(term, num_children));
}

std::string Cvc5Term::print_value_as(SortKind /* sk */) const
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Cannot use print_value_as on a non-value term.");
  }
  return term.toString();
}

::cvc5::Term Cvc5Term::get_cvc5_term() const { return term; }

/* end Cvc5Term implementation */

}  // namespace smt
