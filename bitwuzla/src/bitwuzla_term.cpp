/*!
 * \file bitwuzla_term.cpp
 * \brief Bitwuzla implementation of AbsTerm
 * \author Makai Mann
 * \author Samantha Archer
 * \author Áron Ricardo Perez-Lopez
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/bitwuzla_term.h"

#include <bitwuzla/cpp/bitwuzla.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <iterator>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "smt-switch/bitwuzla_sort.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"

namespace smt {

namespace {

// Each operator Bitwuzla supports with the Bitwuzla kind of its
// applications, in the order of the enum, then the kinds only ever looked up
// from the Bitwuzla kind
//
// Both lookups index an array built from this table rather than search it,
// as get_op runs for every node a traversal visits.
constexpr std::pair<Op::Kind, bitwuzla::Kind> kind_pairs[] = {
  { Op::And, bitwuzla::Kind::AND },
  { Op::Or, bitwuzla::Kind::OR },
  { Op::Xor, bitwuzla::Kind::XOR },
  { Op::Not, bitwuzla::Kind::NOT },
  { Op::Implies, bitwuzla::Kind::IMPLIES },
  { Op::Ite, bitwuzla::Kind::ITE },
  { Op::Equal, bitwuzla::Kind::EQUAL },
  { Op::Distinct, bitwuzla::Kind::DISTINCT },
  { Op::Apply, bitwuzla::Kind::APPLY },
  { Op::Concat, bitwuzla::Kind::BV_CONCAT },
  { Op::Extract, bitwuzla::Kind::BV_EXTRACT },
  { Op::BVNot, bitwuzla::Kind::BV_NOT },
  { Op::BVNeg, bitwuzla::Kind::BV_NEG },
  { Op::BVAnd, bitwuzla::Kind::BV_AND },
  { Op::BVOr, bitwuzla::Kind::BV_OR },
  { Op::BVXor, bitwuzla::Kind::BV_XOR },
  { Op::BVNand, bitwuzla::Kind::BV_NAND },
  { Op::BVNor, bitwuzla::Kind::BV_NOR },
  { Op::BVXnor, bitwuzla::Kind::BV_XNOR },
  { Op::BVAdd, bitwuzla::Kind::BV_ADD },
  { Op::BVSub, bitwuzla::Kind::BV_SUB },
  { Op::BVMul, bitwuzla::Kind::BV_MUL },
  { Op::BVUdiv, bitwuzla::Kind::BV_UDIV },
  { Op::BVSdiv, bitwuzla::Kind::BV_SDIV },
  { Op::BVUrem, bitwuzla::Kind::BV_UREM },
  { Op::BVSrem, bitwuzla::Kind::BV_SREM },
  { Op::BVSmod, bitwuzla::Kind::BV_SMOD },
  { Op::BVShl, bitwuzla::Kind::BV_SHL },
  { Op::BVAshr, bitwuzla::Kind::BV_ASHR },
  { Op::BVLshr, bitwuzla::Kind::BV_SHR },
  { Op::BVComp, bitwuzla::Kind::BV_COMP },
  { Op::BVUlt, bitwuzla::Kind::BV_ULT },
  { Op::BVUle, bitwuzla::Kind::BV_ULE },
  { Op::BVUgt, bitwuzla::Kind::BV_UGT },
  { Op::BVUge, bitwuzla::Kind::BV_UGE },
  { Op::BVSlt, bitwuzla::Kind::BV_SLT },
  { Op::BVSle, bitwuzla::Kind::BV_SLE },
  { Op::BVSgt, bitwuzla::Kind::BV_SGT },
  { Op::BVSge, bitwuzla::Kind::BV_SGE },
  { Op::Zero_Extend, bitwuzla::Kind::BV_ZERO_EXTEND },
  { Op::Sign_Extend, bitwuzla::Kind::BV_SIGN_EXTEND },
  { Op::Repeat, bitwuzla::Kind::BV_REPEAT },
  { Op::Rotate_Left, bitwuzla::Kind::BV_ROLI },
  { Op::Rotate_Right, bitwuzla::Kind::BV_RORI },
  { Op::Select, bitwuzla::Kind::ARRAY_SELECT },
  { Op::Store, bitwuzla::Kind::ARRAY_STORE },
  { Op::Forall, bitwuzla::Kind::FORALL },
  { Op::Exists, bitwuzla::Kind::EXISTS },
  { Op::Equal, bitwuzla::Kind::IFF },
};

/** One more than the largest kind in the table, which Bitwuzla's own count
 *  of kinds cannot give, as its release builds leave that out
 */
constexpr std::size_t table_kinds()
{
  std::size_t n = 0;
  for (const std::pair<Op::Kind, bitwuzla::Kind> & row : kind_pairs)
  {
    n = std::max(n, static_cast<std::size_t>(row.second) + 1);
  }
  return n;
}
constexpr std::size_t num_kinds = table_kinds();

// The row of each operator kind, the first that has it, or -1 for one
// Bitwuzla does not support, and the operator of each Bitwuzla kind, from the
// last row that has it, or Op::NONE for one that no operator stands for
struct KindTables
{
  constexpr KindTables()
  {
    for (int & row : rows)
    {
      row = -1;
    }
    for (std::size_t i = 0; i < std::size(kind_pairs); ++i)
    {
      const std::pair<Op::Kind, bitwuzla::Kind> & row = kind_pairs[i];
      if (rows[row.first] < 0)
      {
        rows[row.first] = static_cast<int>(i);
      }
      op_kinds[static_cast<std::size_t>(row.second)] = row.first;
    }
  }
  std::array<int, Op::num_kinds> rows = {};
  std::array<Op::Kind, num_kinds> op_kinds = {};
};
constexpr KindTables kind_tables;

/** The operator of the applications of kind
 *  @throws NotImplementedException for a kind that no operator stands for
 */
Op::Kind to_op_kind(bitwuzla::Kind kind)
{
  const std::size_t i = static_cast<std::size_t>(kind);
  if (i >= num_kinds || kind_tables.op_kinds[i] == Op::NONE)
  {
    throw NotImplementedException(
        "smt-switch has no operator for the Bitwuzla kind "
        + std::to_string(kind));
  }
  return kind_tables.op_kinds[i];
}

/** The Bitwuzla kind of the applications of k
 *  @throws IncorrectUsageException for Op::NONE or an out-of-range value
 *  @throws NotImplementedException for an operator Bitwuzla does not support
 */
bitwuzla::Kind to_bitwuzla_kind(Op::Kind k)
{
  if (k == Op::NONE || k >= Op::num_kinds)
  {
    throw IncorrectUsageException("Can't make a term with the operator kind "
                                  + std::to_string(static_cast<int>(k)));
  }
  if (kind_tables.rows[k] < 0)
  {
    throw NotImplementedException("Bitwuzla does not support the operator "
                                  + smt::to_string(k));
  }
  return kind_pairs[kind_tables.rows[k]].second;
}

}  // namespace

BzlaTerm::BzlaTerm(const std::shared_ptr<BzlaTermManager> & manager,
                   bitwuzla::Term t)
    : tm(manager), term(std::move(t))
{
}

BzlaTerm::BzlaTerm(const std::shared_ptr<BzlaTermManager> & manager,
                   const Op & op,
                   const std::vector<bitwuzla::Term> & children)
    : tm(manager),
      term(manager->mk_term(
          to_bitwuzla_kind(op.kind()),
          children,
          std::vector<std::uint64_t>(op.indices.begin(), op.indices.end())))
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

  Op::Kind op_kind = to_op_kind(bkind);

  if (get_num_indices(op_kind) > 0)
  {
    std::size_t num_indices = term.num_indices();
    std::vector<std::uint64_t> indices = term.indices();
    std::uint64_t idx0 = indices[0];
    if (num_indices == 1)
    {
      return Op(op_kind, idx0);
    }
    else
    {
      std::uint64_t idx1 = indices[1];
      return Op(op_kind, idx0, idx1);
    }
  }

  return Op(op_kind);
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

std::uint64_t BzlaTerm::to_int() const { return bits_to_uint64(to_bits()); }

std::int64_t BzlaTerm::to_signed_int() const
{
  return bits_to_int64(to_bits());
}

std::string BzlaTerm::to_bits() const
{
  if (!term.is_value() || !term.sort().is_bv())
  {
    throw IncorrectUsageException(
        "Can't get a bitstring from a term that is not a bit-vector value");
  }
  return term.value<std::string>(2);
}

bool BzlaTerm::to_bool() const
{
  if (!term.is_value() || !term.sort().is_bool())
  {
    throw IncorrectUsageException("Can't convert " + term.str()
                                  + " to a Boolean: it is not a Boolean value");
  }
  return term.value<bool>();
}

std::size_t BzlaTerm::get_num_children() const { return term.num_children(); }

Term BzlaTerm::get_child(std::size_t i) const
{
  return std::make_shared<BzlaTerm>(tm, term[i]);
}

std::string BzlaTerm::print_value_as(SortKind /* sk */) const
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Can't use print_value_as on a term that is not a value");
  }
  return to_string();
}

const bitwuzla::Term BzlaTerm::get_bitwuzla_term() const { return term; }

}  // namespace smt
