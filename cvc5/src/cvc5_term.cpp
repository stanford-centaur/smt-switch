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

#include "api/cpp/cvc5.h"
#include "assert.h"
#include "cvc5_sort.h"
#include "exceptions.h"

namespace smt {

// the kinds cvc5 needs to build an OpTerm for an indexed op
const std::unordered_map<::cvc5::Kind, size_t> kind2numindices(
    { { ::cvc5::BITVECTOR_EXTRACT, 2 },
      { ::cvc5::BITVECTOR_ZERO_EXTEND, 1 },
      { ::cvc5::BITVECTOR_SIGN_EXTEND, 1 },
      { ::cvc5::BITVECTOR_REPEAT, 1 },
      { ::cvc5::BITVECTOR_ROTATE_LEFT, 1 },
      { ::cvc5::BITVECTOR_ROTATE_RIGHT, 1 },
      { ::cvc5::INT_TO_BITVECTOR, 1 } });

const std::unordered_map<::cvc5::Kind, PrimOp> kind2primop(
    { { ::cvc5::AND, And },
      { ::cvc5::OR, Or },
      { ::cvc5::XOR, Xor },
      { ::cvc5::NOT, Not },
      { ::cvc5::IMPLIES, Implies },
      { ::cvc5::ITE, Ite },
      { ::cvc5::EQUAL, Equal },
      { ::cvc5::DISTINCT, Distinct },
      /* Uninterpreted Functions */
      { ::cvc5::APPLY_UF, Apply },
      /* Arithmetic Theories */
      { ::cvc5::ADD, Plus },
      { ::cvc5::SUB, Minus },
      { ::cvc5::NEG, Negate },
      { ::cvc5::MULT, Mult },
      { ::cvc5::DIVISION, Div },
      { ::cvc5::LT, Lt },
      { ::cvc5::LEQ, Le },
      { ::cvc5::GT, Gt },
      { ::cvc5::GEQ, Ge },
      { ::cvc5::INTS_MODULUS, Mod },
      { ::cvc5::ABS, Abs },
      { ::cvc5::POW, Pow },
      { ::cvc5::TO_REAL, To_Real },
      { ::cvc5::TO_INTEGER, To_Int },
      { ::cvc5::IS_INTEGER, Is_Int },
      /* Fixed Size BitVector Theory */
      { ::cvc5::BITVECTOR_CONCAT, Concat },
      // Indexed Op
      { ::cvc5::BITVECTOR_EXTRACT, Extract },
      { ::cvc5::BITVECTOR_NOT, BVNot },
      { ::cvc5::BITVECTOR_NEG, BVNeg },
      { ::cvc5::BITVECTOR_AND, BVAnd },
      { ::cvc5::BITVECTOR_OR, BVOr },
      { ::cvc5::BITVECTOR_XOR, BVXor },
      { ::cvc5::BITVECTOR_NAND, BVNand },
      { ::cvc5::BITVECTOR_NOR, BVNor },
      { ::cvc5::BITVECTOR_XNOR, BVXnor },
      { ::cvc5::BITVECTOR_COMP, BVComp },
      { ::cvc5::BITVECTOR_ADD, BVAdd },
      { ::cvc5::BITVECTOR_SUB, BVSub },
      { ::cvc5::BITVECTOR_MULT, BVMul },
      { ::cvc5::BITVECTOR_UDIV, BVUdiv },
      { ::cvc5::BITVECTOR_SDIV, BVSdiv },
      { ::cvc5::BITVECTOR_UREM, BVUrem },
      { ::cvc5::BITVECTOR_SREM, BVSrem },
      { ::cvc5::BITVECTOR_SMOD, BVSmod },
      { ::cvc5::BITVECTOR_SHL, BVShl },
      { ::cvc5::BITVECTOR_ASHR, BVAshr },
      { ::cvc5::BITVECTOR_LSHR, BVLshr },
      { ::cvc5::BITVECTOR_ULT, BVUlt },
      { ::cvc5::BITVECTOR_ULE, BVUle },
      { ::cvc5::BITVECTOR_UGT, BVUgt },
      { ::cvc5::BITVECTOR_UGE, BVUge },
      { ::cvc5::BITVECTOR_SLT, BVSlt },
      { ::cvc5::BITVECTOR_SLE, BVSle },
      { ::cvc5::BITVECTOR_SGT, BVSgt },
      { ::cvc5::BITVECTOR_SGE, BVSge },
      // Indexed Op
      { ::cvc5::BITVECTOR_ZERO_EXTEND, Zero_Extend },
      // Indexed Op
      { ::cvc5::BITVECTOR_SIGN_EXTEND, Sign_Extend },
      // Indexed Op
      { ::cvc5::BITVECTOR_REPEAT, Repeat },
      // Indexed Op
      { ::cvc5::BITVECTOR_ROTATE_LEFT, Rotate_Left },
      // Indexed Op
      { ::cvc5::BITVECTOR_ROTATE_RIGHT, Rotate_Right },
      // Conversion
      { ::cvc5::BITVECTOR_TO_NAT, BV_To_Nat },
      // String Op
      { ::cvc5::STRING_LT, StrLt },
      { ::cvc5::STRING_LEQ, StrLeq },
      { ::cvc5::STRING_LENGTH, StrLen },
      { ::cvc5::STRING_CONCAT, StrConcat },
      // Indexed Op
      { ::cvc5::INT_TO_BITVECTOR, Int_To_BV },
      { ::cvc5::SELECT, Select },
      { ::cvc5::STORE, Store },
      { ::cvc5::FORALL, Forall },
      { ::cvc5::EXISTS, Exists },
      // Datatype
      { ::cvc5::APPLY_CONSTRUCTOR, Apply_Constructor },
      { ::cvc5::APPLY_TESTER, Apply_Tester },
      { ::cvc5::APPLY_SELECTOR, Apply_Selector } });

// struct for hashing
std::hash<cvc5::Term> termhash;

/* Cvc5TermIter implementation */
Cvc5TermIter & Cvc5TermIter::operator=(const Cvc5TermIter & it)
{
  term = it.term;
  pos = it.pos;
  return *this;
}

void Cvc5TermIter::operator++() { pos++; }

const Term Cvc5TermIter::operator*()
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
  if (t.getKind() == ::cvc5::VARIABLE_LIST)
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

bool Cvc5TermIter::operator==(const Cvc5TermIter & it)
{
  return term == it.term && pos == it.pos;
}

bool Cvc5TermIter::operator!=(const Cvc5TermIter & it)
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

std::size_t Cvc5Term::hash() const { return termhash(term); }

std::size_t Cvc5Term::get_id() const { return term.getId(); }

bool Cvc5Term::compare(const Term & absterm) const
{
  std::shared_ptr<Cvc5Term> other = std::static_pointer_cast<Cvc5Term>(absterm);
  return term == other->term;
}

Op Cvc5Term::get_op() const
{
  if (!term.hasOp())
  {
    // return a null op
    return Op();
  }

  cvc5::Op cvc5_op = term.getOp();
  cvc5::Kind cvc5_kind = cvc5_op.getKind();

  // special cases
  if (cvc5_kind == cvc5::Kind::CONST_ARRAY)
  {
    // constant array is a value in smt-switch
    return Op();
  }

  // implementation checking
  if (kind2primop.find(cvc5_kind) == kind2primop.end())
  {
    throw NotImplementedException("get_op not implemented for cvc5 Kind "
                                  + cvc5::kindToString(cvc5_kind));
  }
  PrimOp po = kind2primop.at(cvc5_kind);

  // create an smt-switch Op and return it
  if (cvc5_op.isIndexed())
  {
    if (kind2numindices.find(cvc5_kind) == kind2numindices.end())
    {
      throw NotImplementedException("get_op not implemented for cvc5 Kind "
                                    + cvc5::kindToString(cvc5_kind));
    }
    size_t num_indices = kind2numindices.at(cvc5_kind);
    if (num_indices == 1)
    {
      uint32_t idx0 = std::stoul(cvc5_op[0].toString());
      return Op(po, idx0);
    }
    else
    {
      assert(num_indices == 2);
      std::pair<uint32_t, uint32_t> indices = {
        std::stoul(cvc5_op[0].toString()), std::stoul(cvc5_op[1].toString())
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
  return (k == ::cvc5::CONSTANT || k == ::cvc5::VARIABLE);
}

bool Cvc5Term::is_param() const { return (term.getKind() == ::cvc5::VARIABLE); }

bool Cvc5Term::is_symbolic_const() const
{
  return (term.getKind() == ::cvc5::CONSTANT && !term.getSort().isFunction());
}

bool Cvc5Term::is_value() const
{
  // checking all possible const types for future-proofing
  // not all these sorts are even supported at this time
  ::cvc5::Kind k = term.getKind();
  return ((k == ::cvc5::CONST_BOOLEAN) || (k == ::cvc5::CONST_BITVECTOR)
          || (k == ::cvc5::CONST_RATIONAL) || (k == ::cvc5::CONST_FLOATINGPOINT)
          || (k == ::cvc5::CONST_ROUNDINGMODE) || (k == ::cvc5::CONST_STRING)
          || (k == ::cvc5::CONST_ARRAY));
}

std::string Cvc5Term::to_string() { return term.toString(); }

std::wstring Cvc5Term::getStringValue() const { return term.getStringValue(); }

uint64_t Cvc5Term::to_int() const
{
  std::string val = term.toString();
  ::cvc5::Sort sort = term.getSort();

  // process smt-lib bit-vector format
  if (sort.isBitVector())
  {
    if (val.find("(_ bv") == std::string::npos)
    {
      std::string msg = val;
      msg += " is not a constant term, can't convert to int.";
      throw IncorrectUsageException(msg.c_str());
    }
    val = val.substr(5, val.length());
    val = val.substr(0, val.find(" "));
  }

  try
  {
    return std::stoi(val);
  }
  catch (std::exception const & e)
  {
    std::string msg("Term ");
    msg += val;
    msg += " does not contain an integer representable by a machine int.";
    throw IncorrectUsageException(msg.c_str());
  }
}

/** Iterators for traversing the children
 */
TermIter Cvc5Term::begin() { return TermIter(new Cvc5TermIter(term, 0)); }

TermIter Cvc5Term::end()
{
  uint32_t num_children = term.getNumChildren();
  if (term.getKind() == ::cvc5::Kind::CONST_ARRAY)
  {
    // base of constant array is the child
    num_children++;
  }
  return TermIter(new Cvc5TermIter(term, num_children));
}

std::string Cvc5Term::print_value_as(SortKind sk)
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Cannot use print_value_as on a non-value term.");
  }
  return term.toString();
}

/* end Cvc5Term implementation */

}  // namespace smt
