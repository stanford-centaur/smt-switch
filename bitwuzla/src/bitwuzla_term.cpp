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

// include standard version of open_memstream
// for compatability with FreeBSD / Darwin which doesn't support it natively
extern "C" {
#include "memstream.h"
}

#include <sstream>

#include "bitwuzla_term.h"

using namespace std;

namespace std {
// specialize the hash template
template <>
struct hash<bitwuzla::Kind>
{
  size_t operator()(const bitwuzla::Kind bk) const
  {
    return static_cast<std::size_t>(bk);
  }
};
}  // namespace std

namespace smt {

const std::unordered_map<bitwuzla::Kind, PrimOp> bkind2primop(
    { /* Core Theory */
      { bitwuzla::Kind::AND, And },
      { bitwuzla::Kind::OR, Or },
      { bitwuzla::Kind::XOR, Xor },
      { bitwuzla::Kind::NOT, Not },
      // needs to be translated
      { bitwuzla::Kind::IMPLIES, Implies },
      { bitwuzla::Kind::IFF, Equal },
      { bitwuzla::Kind::ITE, Ite },
      { bitwuzla::Kind::EQUAL, Equal },
      { bitwuzla::Kind::DISTINCT, Distinct },
      /* Uninterpreted Functions */
      { bitwuzla::Kind::APPLY, Apply },
      /* Fixed Size BitVector Theory */
      { bitwuzla::Kind::BV_CONCAT, Concat },
      { bitwuzla::Kind::BV_EXTRACT, Extract },
      { bitwuzla::Kind::BV_NOT, BVNot },
      { bitwuzla::Kind::BV_NEG, BVNeg },
      { bitwuzla::Kind::BV_AND, BVAnd },
      { bitwuzla::Kind::BV_OR, BVOr },
      { bitwuzla::Kind::BV_XOR, BVXor },
      { bitwuzla::Kind::BV_NAND, BVNand },
      { bitwuzla::Kind::BV_NOR, BVNor },
      { bitwuzla::Kind::BV_XNOR, BVXnor },
      { bitwuzla::Kind::BV_ADD, BVAdd },
      { bitwuzla::Kind::BV_SUB, BVSub },
      { bitwuzla::Kind::BV_MUL, BVMul },
      { bitwuzla::Kind::BV_UDIV, BVUdiv },
      { bitwuzla::Kind::BV_SDIV, BVSdiv },
      { bitwuzla::Kind::BV_UREM, BVUrem },
      { bitwuzla::Kind::BV_SREM, BVSrem },
      { bitwuzla::Kind::BV_SMOD, BVSmod },
      { bitwuzla::Kind::BV_SHL, BVShl },
      { bitwuzla::Kind::BV_ASHR, BVAshr },
      { bitwuzla::Kind::BV_SHR, BVLshr },
      { bitwuzla::Kind::BV_COMP, BVComp },
      { bitwuzla::Kind::BV_ULT, BVUlt },
      { bitwuzla::Kind::BV_ULE, BVUle },
      { bitwuzla::Kind::BV_UGT, BVUgt },
      { bitwuzla::Kind::BV_UGE, BVUge },
      { bitwuzla::Kind::BV_SLT, BVSlt },
      { bitwuzla::Kind::BV_SLE, BVSle },
      { bitwuzla::Kind::BV_SGT, BVSgt },
      { bitwuzla::Kind::BV_SGE, BVSge },
      { bitwuzla::Kind::BV_ZERO_EXTEND, Zero_Extend },  // Indexed
      { bitwuzla::Kind::BV_SIGN_EXTEND, Sign_Extend },  // Indexed
      { bitwuzla::Kind::BV_REPEAT, Repeat },            // Indexed
      { bitwuzla::Kind::BV_ROLI, Rotate_Left },         // Indexed
      { bitwuzla::Kind::BV_RORI, Rotate_Right },        // Indexed
                                                      /* Array Theory */
      { bitwuzla::Kind::ARRAY_SELECT, Select },
      { bitwuzla::Kind::ARRAY_STORE, Store },
      /* Quantifiers */
      { bitwuzla::Kind::FORALL, Forall },
      { bitwuzla::Kind::EXISTS, Exists } });

const unordered_set<PrimOp> indexed_ops(
    { Extract, Zero_Extend, Sign_Extend, Repeat, Rotate_Left, Rotate_Right });

/*  start BzlaTermIter implementation */

BzlaTermIter & BzlaTermIter::operator=(const BzlaTermIter & it)
{
  terms = it.terms;
  idx = it.idx;
  return *this;
}

void BzlaTermIter::operator++()
{
  idx++;
}

const Term BzlaTermIter::operator*()
{
  assert(idx < terms.num_children());
  return make_shared<BzlaTerm>(terms[idx]);
}

TermIterBase * BzlaTermIter::clone() const
{
  return new BzlaTermIter(terms, idx);
}

bool BzlaTermIter::operator==(const BzlaTermIter & it) { return equal(it); }

bool BzlaTermIter::operator!=(const BzlaTermIter & it) { return !equal(it); }

bool BzlaTermIter::equal(const TermIterBase & other) const
{
  const BzlaTermIter & bti = static_cast<const BzlaTermIter &>(other);
  if (idx != bti.idx || terms.num_children() != bti.terms.num_children())
  {
    // do a cheap equality test first
    return false;
  }
  // more expensive vector equality
  return terms == bti.terms;
}

/*  end BzlaTermIter implementation */

BzlaTerm::BzlaTerm(const bitwuzla::Term t) : term(t) {}

BzlaTerm::~BzlaTerm() {}

std::size_t BzlaTerm::hash() const { return std::hash<bitwuzla::Term>{}(term); }

// hash is unique in bitwuzla
std::size_t BzlaTerm::get_id() const { return std::hash<bitwuzla::Term>{}(term); }

bool BzlaTerm::compare(const Term & absterm) const
{
  shared_ptr<BzlaTerm> bterm = static_pointer_cast<BzlaTerm>(absterm);
  // in bitwuzla, the pointers will be equivalent iff the terms are equivalent
  return term == bterm->term;
}

Op BzlaTerm::get_op() const
{
  if (term.is_const() || term.is_variable() || term.is_value())
  {
    return Op();
  }

  bitwuzla::Kind bkind = term.kind();
  if (bkind == bitwuzla::Kind::CONST_ARRAY) 
  {
    return Op();
  }

  auto it = bkind2primop.find(bkind);
  if (it == bkind2primop.end())
  {
    throw NotImplementedException("Unknown operator in bitwuzla backend.");
  }

  PrimOp po = it->second;

  if (indexed_ops.find(po) != indexed_ops.end())
  {
    size_t num_indices = term.num_indices();
    assert(num_indices > 0);
    assert(num_indices <= 2);
    std::vector<uint64_t> indices = term.indices();
    uint32_t idx0 = indices[0];
    if (num_indices == 1)
    {
      return Op(po, idx0);
    }
    else
    {
      uint32_t idx1 = indices[1];
      return Op(po, idx0, idx1);
    }
  }

  return Op(po);
}

Sort BzlaTerm::get_sort() const
{
  return make_shared<BzlaSort>(term.sort());
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
  // return (bitwuzla_term_is_const(term) && !bitwuzla_term_is_fun(term));
  return (term.is_const() && !(term.sort().is_fun()));
}

bool BzlaTerm::is_value() const
{
  return term.is_value();
}

std::string BzlaTerm::to_string() { 
  return term.str(); 
}

uint64_t BzlaTerm::to_int() const
{
  if (!term.sort().is_bv())
  {
    throw IncorrectUsageException(
        "Can't get bitstring from a non-bitvector value term.");
  }
  uint64_t width = term.sort().bv_size();
  if (width > 64)
  {
    string msg("Can't represent a bit-vector of size ");
    msg += std::to_string(width);
    msg += " in a uint64_t";
    throw IncorrectUsageException(msg.c_str());
  }
  string bits = term.str();
  // special case -- 1-bit bit-vectors are
  // printed as Booleans in bitwuzla.
  if (bits == "true") {
    return 1;
  } else if (bits == "false") {
    return 0;
  }
  assert(bits.substr(0, 2) == "#b");
  bits = bits.substr(2, bits.length());
  string::size_type sz = 0;
  return std::stoull(bits, &sz, 2);
}

TermIter BzlaTerm::begin()
{
  return TermIter(
      new BzlaTermIter(term, 0));
}

TermIter BzlaTerm::end()
{
  size_t num_children = term.num_children();
  return TermIter(
      new BzlaTermIter(term, num_children));
}

string BzlaTerm::print_value_as(SortKind sk)
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Cannot use print_value_as on a non-value term.");
  }

  if (term.sort().is_bv())
  {
    uint64_t width = term.sort().bv_size();
    if (width == 1 && sk == BV)
    {
      if (term.is_bv_value_one())
      {
        return "#b1";
      }
      else
      {
        return "#b0";
      }
    }
    else
    {
      return to_string();
    }
  }
  else
  {
    return to_string();
  }
}
}  // namespace smt
