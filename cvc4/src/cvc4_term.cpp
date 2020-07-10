/*********************                                                        */
/*! \file cvc4_term.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief CVC4 implementation of AbsTerm
**
**
**/

#include "assert.h"

#include "api/cvc4cpp.h"

#include "exceptions.h"

#include "cvc4_sort.h"
#include "cvc4_term.h"

namespace smt {

// the kinds CVC4 needs to build an OpTerm for an indexed op
const std::unordered_map<::CVC4::api::Kind, size_t> kind2numindices(
    { { ::CVC4::api::BITVECTOR_EXTRACT, 2 },
      { ::CVC4::api::BITVECTOR_ZERO_EXTEND, 1 },
      { ::CVC4::api::BITVECTOR_SIGN_EXTEND, 1 },
      { ::CVC4::api::BITVECTOR_REPEAT, 1 },
      { ::CVC4::api::BITVECTOR_ROTATE_LEFT, 1 },
      { ::CVC4::api::BITVECTOR_ROTATE_RIGHT, 1 },
      { ::CVC4::api::INT_TO_BITVECTOR, 1 } });

const std::unordered_map<::CVC4::api::Kind, PrimOp> kind2primop(
    { { ::CVC4::api::AND, And },
      { ::CVC4::api::OR, Or },
      { ::CVC4::api::XOR, Xor },
      { ::CVC4::api::NOT, Not },
      { ::CVC4::api::IMPLIES, Implies },
      { ::CVC4::api::ITE, Ite },
      { ::CVC4::api::EQUAL, Equal },
      { ::CVC4::api::DISTINCT, Distinct },
      /* Uninterpreted Functions */
      { ::CVC4::api::APPLY_UF, Apply },
      /* Arithmetic Theories */
      { ::CVC4::api::PLUS, Plus },
      { ::CVC4::api::MINUS, Minus },
      { ::CVC4::api::UMINUS, Negate },
      { ::CVC4::api::MULT, Mult },
      { ::CVC4::api::DIVISION, Div },
      { ::CVC4::api::LT, Lt },
      { ::CVC4::api::LEQ, Le },
      { ::CVC4::api::GT, Gt },
      { ::CVC4::api::GEQ, Ge },
      { ::CVC4::api::INTS_MODULUS, Mod },
      { ::CVC4::api::ABS, Abs },
      { ::CVC4::api::POW, Pow },
      { ::CVC4::api::TO_REAL, To_Real },
      { ::CVC4::api::TO_INTEGER, To_Int },
      { ::CVC4::api::IS_INTEGER, Is_Int },
      /* Fixed Size BitVector Theory */
      { ::CVC4::api::BITVECTOR_CONCAT, Concat },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_EXTRACT, Extract },
      { ::CVC4::api::BITVECTOR_NOT, BVNot },
      { ::CVC4::api::BITVECTOR_NEG, BVNeg },
      { ::CVC4::api::BITVECTOR_AND, BVAnd },
      { ::CVC4::api::BITVECTOR_OR, BVOr },
      { ::CVC4::api::BITVECTOR_XOR, BVXor },
      { ::CVC4::api::BITVECTOR_NAND, BVNand },
      { ::CVC4::api::BITVECTOR_NOR, BVNor },
      { ::CVC4::api::BITVECTOR_XNOR, BVXnor },
      { ::CVC4::api::BITVECTOR_COMP, BVComp },
      { ::CVC4::api::BITVECTOR_PLUS, BVAdd },
      { ::CVC4::api::BITVECTOR_SUB, BVSub },
      { ::CVC4::api::BITVECTOR_MULT, BVMul },
      { ::CVC4::api::BITVECTOR_UDIV, BVUdiv },
      { ::CVC4::api::BITVECTOR_SDIV, BVSdiv },
      { ::CVC4::api::BITVECTOR_UREM, BVUrem },
      { ::CVC4::api::BITVECTOR_SREM, BVSrem },
      { ::CVC4::api::BITVECTOR_SMOD, BVSmod },
      { ::CVC4::api::BITVECTOR_SHL, BVShl },
      { ::CVC4::api::BITVECTOR_ASHR, BVAshr },
      { ::CVC4::api::BITVECTOR_LSHR, BVLshr },
      { ::CVC4::api::BITVECTOR_ULT, BVUlt },
      { ::CVC4::api::BITVECTOR_ULE, BVUle },
      { ::CVC4::api::BITVECTOR_UGT, BVUgt },
      { ::CVC4::api::BITVECTOR_UGE, BVUge },
      { ::CVC4::api::BITVECTOR_SLT, BVSlt },
      { ::CVC4::api::BITVECTOR_SLE, BVSle },
      { ::CVC4::api::BITVECTOR_SGT, BVSgt },
      { ::CVC4::api::BITVECTOR_SGE, BVSge },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_ZERO_EXTEND, Zero_Extend },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_SIGN_EXTEND, Sign_Extend },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_REPEAT, Repeat },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_ROTATE_LEFT, Rotate_Left },
      // Indexed Op
      { ::CVC4::api::BITVECTOR_ROTATE_RIGHT, Rotate_Right },
      { ::CVC4::api::SELECT, Select },
      { ::CVC4::api::STORE, Store },
      { ::CVC4::api::FORALL, Forall },
      { ::CVC4::api::EXISTS, Exists },
      // Datatype
      { ::CVC4::api::APPLY_CONSTRUCTOR, Apply_Constructor},
      { ::CVC4::api::APPLY_TESTER, Apply_Tester},
      { ::CVC4::api::APPLY_SELECTOR, Apply_Selector}});

// struct for hashing
CVC4::api::TermHashFunction termhash;

/* CVC4TermIter implementation */
CVC4TermIter & CVC4TermIter::operator=(const CVC4TermIter & it)
{
  term = it.term;
  pos = it.pos;
  return *this;
}

void CVC4TermIter::operator++() { pos++; }

const Term CVC4TermIter::operator*()
{
  if (pos == term.getNumChildren()
      && term.getKind() == ::CVC4::api::Kind::CONST_ARRAY)
  {
    return std::make_shared<CVC4Term>(term.getConstArrayBase());
  }
  // special-case for BOUND_VAR_LIST -- parameters bound by a quantifier
  // smt-switch guarantees that the length is only one by construction
  ::CVC4::api::Term t = term[pos];
  if (t.getKind() == ::CVC4::api::BOUND_VAR_LIST)
  {
    if (t.getNumChildren() != 1)
    {
      // smt-switch should only allow binding one parameter
      // otherwise, we need to flatten arbitrary nestings of quantifiers and
      // BOUND_VAR_LISTs for term iteration
      throw InternalSolverException(
          "Expected exactly one bound variable in CVC4 BOUND_VAR_LIST");
    }
    return std::make_shared<CVC4Term>(t[0]);
  }
  return std::make_shared<CVC4Term>(t);
}

TermIterBase * CVC4TermIter::clone() const
{
  return new CVC4TermIter(term, pos);
}

bool CVC4TermIter::operator==(const CVC4TermIter & it)
{
  return term == it.term && pos == it.pos;
}

bool CVC4TermIter::operator!=(const CVC4TermIter & it)
{
  return term != term || pos != it.pos;
}

bool CVC4TermIter::equal(const TermIterBase & other) const
{
  const CVC4TermIter & cti = static_cast<const CVC4TermIter &>(other);
  return term == cti.term && pos == cti.pos;
}

/* end CVC4TermIter implementation */

/* CVC4Term implementation */

std::size_t CVC4Term::hash() const
{
  return termhash(term);
}

bool CVC4Term::compare(const Term & absterm) const
{
  std::shared_ptr<CVC4Term> other =
    std::static_pointer_cast<CVC4Term>(absterm);
  return term == other->term;
}

Op CVC4Term::get_op() const
{
  if (!term.hasOp())
  {
    // return a null op
    return Op();
  }

  CVC4::api::Op cvc4_op = term.getOp();
  CVC4::api::Kind cvc4_kind = cvc4_op.getKind();

  // special cases
  if (cvc4_kind == CVC4::api::Kind::CONST_ARRAY)
  {
    // constant array is a value in smt-switch
    return Op();
  }

  // implementation checking
  if (kind2primop.find(cvc4_kind) == kind2primop.end())
  {
    throw NotImplementedException("get_op not implemented for CVC4 Kind "
                                  + CVC4::api::kindToString(cvc4_kind));
  }
  PrimOp po = kind2primop.at(cvc4_kind);

  // create an smt-switch Op and return it
  if (cvc4_op.isIndexed())
  {
    if (kind2numindices.find(cvc4_kind) == kind2numindices.end())
    {
      throw NotImplementedException("get_op not implemented for CVC4 Kind "
                                    + CVC4::api::kindToString(cvc4_kind));
    }
    size_t num_indices = kind2numindices.at(cvc4_kind);
    if (num_indices == 1)
    {
      uint32_t idx0 = cvc4_op.getIndices<uint32_t>();
      return Op(po, idx0);
    }
    else
    {
      assert(num_indices == 2);
      std::pair<uint32_t, uint32_t> indices =
          cvc4_op.getIndices<std::pair<uint32_t, uint32_t>>();
      return Op(po, indices.first, indices.second);
    }
  }
  else
  {
    return Op(po);
  }
}

Sort CVC4Term::get_sort() const
{
  return std::make_shared<CVC4Sort> (term.getSort());
}

bool CVC4Term::is_symbol() const
{
  // functions, parameters, and symbolic constants are all symbols
  ::CVC4::api::Kind k = term.getKind();
  return (k == ::CVC4::api::CONSTANT || k == ::CVC4::api::VARIABLE);
}

bool CVC4Term::is_param() const
{
  return (term.getKind() == ::CVC4::api::VARIABLE);
}

bool CVC4Term::is_symbolic_const() const
{
  return (term.getKind() == ::CVC4::api::CONSTANT
          && !term.getSort().isFunction());
}

bool CVC4Term::is_value() const
{
  // checking all possible const types for future-proofing
  // not all these sorts are even supported at this time
  ::CVC4::api::Kind k = term.getKind();
  return ((k == ::CVC4::api::CONST_BOOLEAN)
          || (k == ::CVC4::api::CONST_BITVECTOR)
          || (k == ::CVC4::api::CONST_RATIONAL)
          || (k == ::CVC4::api::CONST_FLOATINGPOINT)
          || (k == ::CVC4::api::CONST_ROUNDINGMODE)
          || (k == ::CVC4::api::CONST_STRING) || (k == ::CVC4::api::CONST_ARRAY));
}

std::string CVC4Term::to_string() { return term.toString(); }

uint64_t CVC4Term::to_int() const
{
  std::string val = term.toString();
  ::CVC4::api::Sort sort = term.getSort();

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
TermIter CVC4Term::begin() { return TermIter(new CVC4TermIter(term, 0)); }

TermIter CVC4Term::end()
{
  uint32_t num_children = term.getNumChildren();
  if (term.getKind() == ::CVC4::api::Kind::CONST_ARRAY)
  {
    // base of constant array is the child
    num_children++;
  }
  return TermIter(new CVC4TermIter(term, num_children));
}

std::string CVC4Term::print_value_as(SortKind sk)
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Cannot use print_value_as on a non-value term.");
  }
  return term.toString();
}

/* end CVC4Term implementation */

}
