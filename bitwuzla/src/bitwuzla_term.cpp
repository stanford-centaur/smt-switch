/*********************                                                        */
/*! \file bitwuzla_term.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bitwuzla implementation of AbsTerm
**
**
**/

#include "bitwuzla_term.h"

#include <bitwuzla/cpp/bitwuzla.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "bitwuzla_sort.h"
#include "exceptions.h"
#include "ops.h"
#include "utils.h"

namespace smt {

namespace {

// Each PrimOp Bitwuzla supports with the Bitwuzla kind of its applications,
// in the order of the enum, then the kinds only ever looked up from the kind
//
// Both lookups index an array built from this table rather than search it,
// as get_op runs for every node a traversal visits.
constexpr std::pair<PrimOp, bitwuzla::Kind> primop_kinds[] = {
  { And, bitwuzla::Kind::AND },
  { Or, bitwuzla::Kind::OR },
  { Xor, bitwuzla::Kind::XOR },
  { Not, bitwuzla::Kind::NOT },
  { Implies, bitwuzla::Kind::IMPLIES },
  { Ite, bitwuzla::Kind::ITE },
  { Equal, bitwuzla::Kind::EQUAL },
  { Distinct, bitwuzla::Kind::DISTINCT },
  { Apply, bitwuzla::Kind::APPLY },
  { Concat, bitwuzla::Kind::BV_CONCAT },
  { Extract, bitwuzla::Kind::BV_EXTRACT },
  { BVNot, bitwuzla::Kind::BV_NOT },
  { BVNeg, bitwuzla::Kind::BV_NEG },
  { BVAnd, bitwuzla::Kind::BV_AND },
  { BVOr, bitwuzla::Kind::BV_OR },
  { BVXor, bitwuzla::Kind::BV_XOR },
  { BVNand, bitwuzla::Kind::BV_NAND },
  { BVNor, bitwuzla::Kind::BV_NOR },
  { BVXnor, bitwuzla::Kind::BV_XNOR },
  { BVAdd, bitwuzla::Kind::BV_ADD },
  { BVSub, bitwuzla::Kind::BV_SUB },
  { BVMul, bitwuzla::Kind::BV_MUL },
  { BVUdiv, bitwuzla::Kind::BV_UDIV },
  { BVSdiv, bitwuzla::Kind::BV_SDIV },
  { BVUrem, bitwuzla::Kind::BV_UREM },
  { BVSrem, bitwuzla::Kind::BV_SREM },
  { BVSmod, bitwuzla::Kind::BV_SMOD },
  { BVShl, bitwuzla::Kind::BV_SHL },
  { BVAshr, bitwuzla::Kind::BV_ASHR },
  { BVLshr, bitwuzla::Kind::BV_SHR },
  { BVComp, bitwuzla::Kind::BV_COMP },
  { BVUlt, bitwuzla::Kind::BV_ULT },
  { BVUle, bitwuzla::Kind::BV_ULE },
  { BVUgt, bitwuzla::Kind::BV_UGT },
  { BVUge, bitwuzla::Kind::BV_UGE },
  { BVSlt, bitwuzla::Kind::BV_SLT },
  { BVSle, bitwuzla::Kind::BV_SLE },
  { BVSgt, bitwuzla::Kind::BV_SGT },
  { BVSge, bitwuzla::Kind::BV_SGE },
  { Zero_Extend, bitwuzla::Kind::BV_ZERO_EXTEND },
  { Sign_Extend, bitwuzla::Kind::BV_SIGN_EXTEND },
  { Repeat, bitwuzla::Kind::BV_REPEAT },
  { Rotate_Left, bitwuzla::Kind::BV_ROLI },
  { Rotate_Right, bitwuzla::Kind::BV_RORI },
  { Select, bitwuzla::Kind::ARRAY_SELECT },
  { Store, bitwuzla::Kind::ARRAY_STORE },
  { Forall, bitwuzla::Kind::FORALL },
  { Exists, bitwuzla::Kind::EXISTS },
  { Equal, bitwuzla::Kind::IFF },
};

/** One more than the largest kind in the table, which Bitwuzla's own count
 *  of kinds cannot give, as its release builds leave that out
 */
constexpr std::size_t table_kinds()
{
  std::size_t n = 0;
  for (const std::pair<PrimOp, bitwuzla::Kind> & row : primop_kinds)
  {
    n = std::max(n, static_cast<std::size_t>(row.second) + 1);
  }
  return n;
}
constexpr std::size_t num_kinds = table_kinds();

// The row of each PrimOp, the first that has it, or -1 for one Bitwuzla does
// not support, and the PrimOp of each kind, from the last row that has it,
// or NUM_OPS_AND_NULL for one that no PrimOp stands for
struct KindTables
{
  constexpr KindTables()
  {
    for (int & row : rows)
    {
      row = -1;
    }
    for (PrimOp & po : primops)
    {
      po = NUM_OPS_AND_NULL;
    }
    for (std::size_t i = 0; i < std::size(primop_kinds); ++i)
    {
      const std::pair<PrimOp, bitwuzla::Kind> & row = primop_kinds[i];
      if (rows[row.first] < 0)
      {
        rows[row.first] = static_cast<int>(i);
      }
      primops[static_cast<std::size_t>(row.second)] = row.first;
    }
  }
  std::array<int, NUM_OPS_AND_NULL> rows = {};
  std::array<PrimOp, num_kinds> primops = {};
};
constexpr KindTables kind_tables;

}  // namespace

bitwuzla::Kind to_bitwuzla_kind(PrimOp po)
{
  if (po >= NUM_OPS_AND_NULL || kind_tables.rows[po] < 0)
  {
    throw NotImplementedException("Bitwuzla does not support the operator "
                                  + to_string(po));
  }
  return primop_kinds[kind_tables.rows[po]].second;
}

PrimOp to_primop(bitwuzla::Kind kind)
{
  const std::size_t i = static_cast<std::size_t>(kind);
  if (i >= num_kinds || kind_tables.primops[i] == NUM_OPS_AND_NULL)
  {
    throw NotImplementedException(
        "smt-switch has no PrimOp for the Bitwuzla kind "
        + std::to_string(kind));
  }
  return kind_tables.primops[i];
}

BzlaTerm::BzlaTerm(bitwuzla::Term t,
                   const std::shared_ptr<BzlaTermManager> & manager)
    : tm(manager), term(std::move(t))
{
}

std::size_t BzlaTerm::hash() const { return std::hash<bitwuzla::Term>{}(term); }

// hash is unique in bitwuzla
std::size_t BzlaTerm::get_id() const
{
  return std::hash<bitwuzla::Term>{}(term);
}

bool BzlaTerm::compare(const Term & absterm) const
{
  std::shared_ptr<BzlaTerm> bterm =
      std::dynamic_pointer_cast<BzlaTerm>(absterm);
  // in bitwuzla, the pointers will be equivalent iff the terms are equivalent
  return bterm && term == bterm->term;
}

Op BzlaTerm::get_op() const
{
  bitwuzla::Kind bkind = term.kind();
  if (term.is_const() || term.is_variable() || term.is_value()
      || bkind == bitwuzla::Kind::CONST_ARRAY)
  {
    return Op();
  }

  PrimOp po = to_primop(bkind);

  if (get_num_indices(po) > 0)
  {
    std::size_t num_indices = term.num_indices();
    std::vector<std::uint64_t> indices = term.indices();
    std::uint64_t idx0 = indices[0];
    if (num_indices == 1)
    {
      return Op(po, idx0);
    }
    else
    {
      std::uint64_t idx1 = indices[1];
      return Op(po, idx0, idx1);
    }
  }

  return Op(po);
}

Sort BzlaTerm::get_sort() const
{
  return std::make_shared<BzlaSort>(term.sort(), tm);
}

bool BzlaTerm::is_symbol() const
{
  // symbols include constants, parameters, and function symbols
  return (term.is_const() || term.is_variable());
}

bool BzlaTerm::is_param() const { return term.is_variable(); }

bool BzlaTerm::is_symbolic_const() const
{
  // in Bitwuzla arrays are functions
  // for smt-switch we consider arrays symbolic constants but not functions
  return (term.is_const() && !(term.sort().is_fun()));
}

bool BzlaTerm::is_value() const
{
  if (term.kind() == bitwuzla::Kind::ARRAY_STORE)
  {
    // SMT-LIB's ArraysEx makes a store of a value into an array value a value
    for (const Term & c : *this)
    {
      if (!c->is_value())
      {
        return false;
      }
    }
    return true;
  }
  return term.is_value() || term.kind() == bitwuzla::Kind::CONST_ARRAY;
}

std::string BzlaTerm::to_string() const { return term.str(); }

/** Returns the bits of a bit-vector value, most significant first */
static std::string bv_value_to_bits(const bitwuzla::Term & term)
{
  if (!term.is_value() || !term.sort().is_bv())
  {
    throw IncorrectUsageException(
        "Can't get bitstring from a term that is not a bit-vector value.");
  }
  return term.value<std::string>(2);
}

std::string BzlaTerm::get_constructor_name() const
{
  throw IncorrectUsageException(
      "Only a constructor or a tester has a constructor name");
}

std::string BzlaTerm::get_param_name() const
{
  if (!is_param())
  {
    throw IncorrectUsageException("Only a param has a param name");
  }
  return term.symbol().value();
}

std::string BzlaTerm::get_selector_name() const
{
  throw IncorrectUsageException("Only a selector has a selector name");
}

std::string BzlaTerm::get_symbol_name() const
{
  if (!term.is_const())
  {
    throw IncorrectUsageException(
        "Only a symbol that is not a param has a symbol name");
  }
  return term.symbol().value();
}

std::uint64_t BzlaTerm::to_int() const
{
  return bits_to_uint64(bv_value_to_bits(term));
}

std::int64_t BzlaTerm::to_signed_int() const
{
  return bits_to_int64(bv_value_to_bits(term));
}

std::size_t BzlaTerm::get_num_children() const { return term.num_children(); }

Term BzlaTerm::get_child(std::size_t i) const
{
  return std::make_shared<BzlaTerm>(term[i], tm);
}

std::string BzlaTerm::print_value_as(SortKind /* sk */) const
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Cannot use print_value_as on a non-value term.");
  }
  return to_string();
}

const bitwuzla::Term BzlaTerm::get_bitwuzla_term() const { return term; }

}  // namespace smt
