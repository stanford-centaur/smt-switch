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

#include "assert.h"

#include "api/cvc5cpp.h"

#include "exceptions.h"

#include "cvc5_sort.h"
#include "cvc5_term.h"

namespace smt {

// the kinds cvc5 needs to build an OpTerm for an indexed op
const std::unordered_map<::cvc5::api::Kind, size_t> kind2numindices(
    { { ::cvc5::api::BITVECTOR_EXTRACT, 2 },
      { ::cvc5::api::BITVECTOR_ZERO_EXTEND, 1 },
      { ::cvc5::api::BITVECTOR_SIGN_EXTEND, 1 },
      { ::cvc5::api::BITVECTOR_REPEAT, 1 },
      { ::cvc5::api::BITVECTOR_ROTATE_LEFT, 1 },
      { ::cvc5::api::BITVECTOR_ROTATE_RIGHT, 1 },
      { ::cvc5::api::INT_TO_BITVECTOR, 1 } });

const std::unordered_map<::cvc5::api::Kind, PrimOp> kind2primop(
    { { ::cvc5::api::AND, And },
      { ::cvc5::api::OR, Or },
      { ::cvc5::api::XOR, Xor },
      { ::cvc5::api::NOT, Not },
      { ::cvc5::api::IMPLIES, Implies },
      { ::cvc5::api::ITE, Ite },
      { ::cvc5::api::EQUAL, Equal },
      { ::cvc5::api::DISTINCT, Distinct },
      /* Uninterpreted Functions */
      { ::cvc5::api::APPLY_UF, Apply },
      /* Arithmetic Theories */
      { ::cvc5::api::PLUS, Plus },
      { ::cvc5::api::MINUS, Minus },
      { ::cvc5::api::UMINUS, Negate },
      { ::cvc5::api::MULT, Mult },
      { ::cvc5::api::DIVISION, Div },
      { ::cvc5::api::LT, Lt },
      { ::cvc5::api::LEQ, Le },
      { ::cvc5::api::GT, Gt },
      { ::cvc5::api::GEQ, Ge },
      { ::cvc5::api::INTS_MODULUS, Mod },
      { ::cvc5::api::ABS, Abs },
      { ::cvc5::api::POW, Pow },
      { ::cvc5::api::TO_REAL, To_Real },
      { ::cvc5::api::TO_INTEGER, To_Int },
      { ::cvc5::api::IS_INTEGER, Is_Int },
      /* Fixed Size BitVector Theory */
      { ::cvc5::api::BITVECTOR_CONCAT, Concat },
      // Indexed Op
      { ::cvc5::api::BITVECTOR_EXTRACT, Extract },
      { ::cvc5::api::BITVECTOR_NOT, BVNot },
      { ::cvc5::api::BITVECTOR_NEG, BVNeg },
      { ::cvc5::api::BITVECTOR_AND, BVAnd },
      { ::cvc5::api::BITVECTOR_OR, BVOr },
      { ::cvc5::api::BITVECTOR_XOR, BVXor },
      { ::cvc5::api::BITVECTOR_NAND, BVNand },
      { ::cvc5::api::BITVECTOR_NOR, BVNor },
      { ::cvc5::api::BITVECTOR_XNOR, BVXnor },
      { ::cvc5::api::BITVECTOR_COMP, BVComp },
      { ::cvc5::api::BITVECTOR_PLUS, BVAdd },
      { ::cvc5::api::BITVECTOR_SUB, BVSub },
      { ::cvc5::api::BITVECTOR_MULT, BVMul },
      { ::cvc5::api::BITVECTOR_UDIV, BVUdiv },
      { ::cvc5::api::BITVECTOR_SDIV, BVSdiv },
      { ::cvc5::api::BITVECTOR_UREM, BVUrem },
      { ::cvc5::api::BITVECTOR_SREM, BVSrem },
      { ::cvc5::api::BITVECTOR_SMOD, BVSmod },
      { ::cvc5::api::BITVECTOR_SHL, BVShl },
      { ::cvc5::api::BITVECTOR_ASHR, BVAshr },
      { ::cvc5::api::BITVECTOR_LSHR, BVLshr },
      { ::cvc5::api::BITVECTOR_ULT, BVUlt },
      { ::cvc5::api::BITVECTOR_ULE, BVUle },
      { ::cvc5::api::BITVECTOR_UGT, BVUgt },
      { ::cvc5::api::BITVECTOR_UGE, BVUge },
      { ::cvc5::api::BITVECTOR_SLT, BVSlt },
      { ::cvc5::api::BITVECTOR_SLE, BVSle },
      { ::cvc5::api::BITVECTOR_SGT, BVSgt },
      { ::cvc5::api::BITVECTOR_SGE, BVSge },
      // Indexed Op
      { ::cvc5::api::BITVECTOR_ZERO_EXTEND, Zero_Extend },
      // Indexed Op
      { ::cvc5::api::BITVECTOR_SIGN_EXTEND, Sign_Extend },
      // Indexed Op
      { ::cvc5::api::BITVECTOR_REPEAT, Repeat },
      // Indexed Op
      { ::cvc5::api::BITVECTOR_ROTATE_LEFT, Rotate_Left },
      // Indexed Op
      { ::cvc5::api::BITVECTOR_ROTATE_RIGHT, Rotate_Right },
      // Conversion
      { ::cvc5::api::BITVECTOR_TO_NAT, BV_To_Nat },
      // Indexed Op
      { ::cvc5::api::INT_TO_BITVECTOR, Int_To_BV },
      { ::cvc5::api::SELECT, Select },
      { ::cvc5::api::STORE, Store },
      { ::cvc5::api::FORALL, Forall },
      { ::cvc5::api::EXISTS, Exists },
      // Datatype
      { ::cvc5::api::APPLY_CONSTRUCTOR, Apply_Constructor },
      { ::cvc5::api::APPLY_TESTER, Apply_Tester },
      { ::cvc5::api::APPLY_SELECTOR, Apply_Selector } });

// struct for hashing
cvc5::api::TermHashFunction termhash;

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
      && term.getKind() == ::cvc5::api::Kind::CONST_ARRAY)
  {
    return std::make_shared<Cvc5Term>(term.getConstArrayBase());
  }
  // special-case for BOUND_VAR_LIST -- parameters bound by a quantifier
  // smt-switch cvc5 backend guarantees that the length is only one by
  // construction
  ::cvc5::api::Term t = term[pos];
  if (t.getKind() == ::cvc5::api::BOUND_VAR_LIST)
  {
    if (t.getNumChildren() != 1)
    {
      // smt-switch cvc5 backend should only allow binding one parameter
      // otherwise, we need to flatten arbitrary nestings of quantifiers and
      // BOUND_VAR_LISTs for term iteration
      throw InternalSolverException(
          "Expected exactly one bound variable in cvc5 BOUND_VAR_LIST");
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

std::size_t Cvc5Term::hash() const
{
  return termhash(term);
}

std::size_t Cvc5Term::get_id() const { return term.getId(); }

bool Cvc5Term::compare(const Term & absterm) const
{
  std::shared_ptr<Cvc5Term> other =
    std::static_pointer_cast<Cvc5Term>(absterm);
  return term == other->term;
}

Op Cvc5Term::get_op() const
{
  if (!term.hasOp())
  {
    // return a null op
    return Op();
  }

  cvc5::api::Op cvc5_op = term.getOp();
  cvc5::api::Kind cvc5_kind = cvc5_op.getKind();

  // special cases
  if (cvc5_kind == cvc5::api::Kind::CONST_ARRAY)
  {
    // constant array is a value in smt-switch
    return Op();
  }

  // implementation checking
  if (kind2primop.find(cvc5_kind) == kind2primop.end())
  {
    throw NotImplementedException("get_op not implemented for cvc5 Kind "
                                  + cvc5::api::kindToString(cvc5_kind));
  }
  PrimOp po = kind2primop.at(cvc5_kind);

  // create an smt-switch Op and return it
  if (cvc5_op.isIndexed())
  {
    if (kind2numindices.find(cvc5_kind) == kind2numindices.end())
    {
      throw NotImplementedException("get_op not implemented for cvc5 Kind "
                                    + cvc5::api::kindToString(cvc5_kind));
    }
    size_t num_indices = kind2numindices.at(cvc5_kind);
    if (num_indices == 1)
    {
      uint32_t idx0 = cvc5_op.getIndices<uint32_t>();
      return Op(po, idx0);
    }
    else
    {
      assert(num_indices == 2);
      std::pair<uint32_t, uint32_t> indices =
          cvc5_op.getIndices<std::pair<uint32_t, uint32_t>>();
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
  return std::make_shared<Cvc5Sort> (term.getSort());
}

bool Cvc5Term::is_symbol() const
{
  // functions, parameters, and symbolic constants are all symbols
  ::cvc5::api::Kind k = term.getKind();
  return (k == ::cvc5::api::CONSTANT || k == ::cvc5::api::VARIABLE);
}

bool Cvc5Term::is_param() const
{
  return (term.getKind() == ::cvc5::api::VARIABLE);
}

bool Cvc5Term::is_symbolic_const() const
{
  return (term.getKind() == ::cvc5::api::CONSTANT
          && !term.getSort().isFunction());
}

bool Cvc5Term::is_value() const
{
  // checking all possible const types for future-proofing
  // not all these sorts are even supported at this time
  ::cvc5::api::Kind k = term.getKind();
  return ((k == ::cvc5::api::CONST_BOOLEAN)
          || (k == ::cvc5::api::CONST_BITVECTOR)
          || (k == ::cvc5::api::CONST_RATIONAL)
          || (k == ::cvc5::api::CONST_FLOATINGPOINT)
          || (k == ::cvc5::api::CONST_ROUNDINGMODE)
          || (k == ::cvc5::api::CONST_STRING) || (k == ::cvc5::api::CONST_ARRAY));
}

std::string Cvc5Term::to_string() { return term.toString(); }

uint64_t Cvc5Term::to_int() const
{
  std::string val = term.toString();
  ::cvc5::api::Sort sort = term.getSort();

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
  if (term.getKind() == ::cvc5::api::Kind::CONST_ARRAY)
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

}
