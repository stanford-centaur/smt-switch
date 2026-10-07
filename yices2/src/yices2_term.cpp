/*********************                                                        */
/*! \file yices2_term.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Yices2 implementation of AbsTerm
**
**
**/

#include "yices2_term.h"

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

#include "exceptions.h"
#include "ops.h"
#include "utils.h"
#include "yices2_sort.h"

using namespace std;

namespace smt {

// Yices2Term implementation

size_t Yices2Term::hash() const
{
  // term_t is a unique id for the term.
  return term;
}

size_t Yices2Term::get_id() const { return term; }

bool Yices2Term::compare(const Term & absterm) const
{
  shared_ptr<Yices2Term> yterm = std::static_pointer_cast<Yices2Term>(absterm);
  return term == yterm->term;
}

/* Yices has no extract constructor. It stores (_ extract high low) as an
 * array of the individual bits, so a BV_ARRAY whose children are the
 * consecutive bits of one bitvector, lowest first, is an extract of it.
 * Returns that bitvector and fills in low and high, or NULL_TERM when the
 * array is some other shape, a concatenation for instance.
 */
static term_t extract_argument(term_t term, uint32_t & low, uint32_t & high)
{
  int32_t num_bits = yices_term_num_children(term);
  if (num_bits < 1)
  {
    return NULL_TERM;
  }

  term_t argument = NULL_TERM;
  for (int32_t i = 0; i < num_bits; i++)
  {
    term_t bit = yices_term_child(term, i);
    if (bit == NULL_TERM || yices_term_constructor(bit) != YICES_BIT_TERM)
    {
      return NULL_TERM;
    }
    int32_t index = yices_proj_index(bit);
    term_t bit_argument = yices_proj_arg(bit);
    if (index < 0 || bit_argument == NULL_TERM)
    {
      return NULL_TERM;
    }
    if (i == 0)
    {
      argument = bit_argument;
      low = static_cast<uint32_t>(index);
    }
    else if (bit_argument != argument
             || static_cast<uint32_t>(index) != low + i)
    {
      // a different bitvector, or a gap: not one contiguous extract
      return NULL_TERM;
    }
  }
  high = low + num_bits - 1;
  return argument;
}

Op Yices2Term::get_op() const
{
  term_constructor_t tc = yices_term_constructor(term);
  std::string sres;
  switch (tc)
  {
    // composite terms
    case YICES_ITE_TERM: return Op(Ite);
    case YICES_APP_TERM:
      if (!is_function)
      {
        return Op(Select);
      }
      return Op(Apply);

    case YICES_EQ_TERM: return Op(Equal);
    case YICES_DISTINCT_TERM: return Op(Distinct);
    case YICES_NOT_TERM: return Op(Not);
    case YICES_OR_TERM: return Op(Or);
    case YICES_XOR_TERM: return Op(Xor);
    case YICES_BV_DIV: return Op(BVUdiv);
    case YICES_BV_REM: return Op(BVUrem);
    case YICES_BV_SDIV: return Op(BVSdiv);
    case YICES_BV_SREM: return Op(BVSrem);
    case YICES_BV_SMOD: return Op(BVSmod);
    case YICES_BV_SHL: return Op(BVShl);
    case YICES_BV_LSHR: return Op(BVLshr);
    case YICES_BV_ASHR: return Op(BVAshr);
    case YICES_BV_GE_ATOM: return Op(BVUge);
    case YICES_BV_SGE_ATOM: return Op(BVSge);
    case YICES_ARITH_GE_ATOM: return Op(Ge);
    case YICES_ABS: return Op(Abs);
    case YICES_RDIV: return Op(Div);
    case YICES_IDIV: return Op(IntDiv);
    case YICES_IMOD: return Op(Mod);
    // // sums
    case YICES_BV_SUM: return Op(BVAdd);
    case YICES_ARITH_SUM:
      /* Arithmetic sums are represented as polynomials,
       * and something like (+ a (-b)) is actually
       * (+ a (* -1 b)), but the individual component
       * (* -1 b) is still of type YICES_ARITH_SUM. To transfer this
       * term, you need to construct the multiply.
       */
      sres = const_to_string();
      sres = sres.substr(sres.find("(") + 1, sres.length());
      sres = sres.substr(0, sres.find(" "));
      if (yices_term_num_children(term) == 1 && sres == "*")
      {
        return Op(Mult);
      }
      return Op(Plus);
    // products
    case YICES_POWER_PRODUCT:
      sres = const_to_string();
      sres = sres.substr(sres.find("(") + 1, sres.length());
      sres = sres.substr(0, sres.find(" "));
      if (sres == "bv-mul")
      {
        return Op(BVMul);
      }
      if (sres == "*")
      {
        return Op(Mult);
      }
      return Op(Pow);
    case YICES_UPDATE_TERM: return Op(Store);
    case YICES_TUPLE_TERM: return Op();
    case YICES_FORALL_TERM: return Op();
    case YICES_LAMBDA_TERM: return Op();
    case YICES_BV_ARRAY: {
      uint32_t low = 0;
      uint32_t high = 0;
      if (extract_argument(term, low, high) != NULL_TERM)
      {
        return Op(Extract, high, low);
      }
      sres = const_to_string();
      sres = sres.substr(sres.find("(") + 1, sres.length());
      sres = sres.substr(0, sres.find(" "));
      if (sres == "bv-concat")
      {
        return Op(Concat);
      }
      return Op();
    }
    case YICES_ARITH_ROOT_ATOM: return Op();
    case YICES_CEIL: return Op();
    case YICES_FLOOR: return Op(To_Int);
    case YICES_IS_INT_ATOM: return Op(Is_Int);
    case YICES_DIVIDES_ATOM: return Op();
    // projections
    case YICES_SELECT_TERM: return Op();
    case YICES_BIT_TERM: return Op();
    // atomic terms
    case YICES_BOOL_CONSTANT: return Op();
    case YICES_ARITH_CONSTANT: return Op();
    case YICES_BV_CONSTANT: return Op();
    case YICES_SCALAR_CONSTANT: return Op();
    case YICES_VARIABLE: return Op();
    case YICES_UNINTERPRETED_TERM: return Op();
    default: return Op();
  }
}

Sort Yices2Term::get_sort() const
{
  if (yices_term_is_function(term))
  {
    // ARRAY
    if (!is_function)
    {
      return Sort(new Yices2Sort(yices_type_of_term(term)));
    }
    // FUNCTION
    else
    {
      return Sort(new Yices2Sort(yices_type_of_term(term), true));
    }
  }

  return Sort(new Yices2Sort(yices_type_of_term(term)));
}

bool Yices2Term::is_symbol() const
{
  // is_function is no help here: make_term sets it on an application of a
  // function as well as on the function. A declared function is an
  // uninterpreted term with no children, so the test below covers it.
  // A parameter is a symbol too, though not a symbolic constant.
  term_constructor_t tc = yices_term_constructor(term);
  return ((tc == YICES_UNINTERPRETED_TERM && yices_term_num_children(term) == 0)
          || tc == YICES_VARIABLE);
}

bool Yices2Term::is_param() const
{
  return yices_term_constructor(term) == YICES_VARIABLE;
}

bool Yices2Term::is_symbolic_const() const
{
  // functions and parameters are not constants
  if (is_function || is_param())
  {
    return false;
  }

  return is_symbol();
}

bool Yices2Term::is_value() const
{
  term_constructor_t tc = yices_term_constructor(term);

  return (tc == YICES_BOOL_CONSTANT || tc == YICES_ARITH_CONSTANT
          || tc == YICES_BV_CONSTANT || tc == YICES_SCALAR_CONSTANT);
}

string Yices2Term::to_string() { return const_to_string(); }

/** Returns the text of an arithmetic constant, e.g. -5 or 1/2 */
static string arith_constant_to_string(term_t term)
{
  char * s = yices_term_to_string(term, UINT32_MAX, 1, 0);
  string val = s;
  yices_free_string(s);
  return val;
}

/** Returns the bits of a bit-vector constant, most significant first */
static string bv_constant_to_bits(term_t term)
{
  const uint32_t width = yices_term_bitsize(term);
  // yices gives the bits least significant first
  vector<int32_t> bits(width);
  yices_bv_const_value(term, bits.data());
  string res;
  for (uint32_t i = width; i > 0; --i)
  {
    res += bits[i - 1] ? '1' : '0';
  }
  return res;
}

uint64_t Yices2Term::to_int() const
{
  if (!is_function)
  {
    term_constructor_t tc = yices_term_constructor(term);
    if (tc == YICES_BV_CONSTANT)
    {
      return bits_to_uint64(bv_constant_to_bits(term));
    }
    else if (tc == YICES_ARITH_CONSTANT)
    {
      return smtlib_int_to_uint64(arith_constant_to_string(term));
    }
  }
  throw IncorrectUsageException(
      "Can't convert a term that is not a bit-vector or arithmetic constant "
      "to an integer");
}

int64_t Yices2Term::to_signed_int() const
{
  if (!is_function)
  {
    term_constructor_t tc = yices_term_constructor(term);
    if (tc == YICES_BV_CONSTANT)
    {
      return bits_to_int64(bv_constant_to_bits(term));
    }
    else if (tc == YICES_ARITH_CONSTANT)
    {
      return smtlib_int_to_int64(arith_constant_to_string(term));
    }
  }
  throw IncorrectUsageException(
      "Can't convert a term that is not a bit-vector or arithmetic constant "
      "to an integer");
}

TermIter Yices2Term::begin()
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

TermIter Yices2Term::end()
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

std::string Yices2Term::print_value_as(SortKind /* sk */)
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Cannot use print_value_as on a non-value term.");
  }
  return to_string();
}

string Yices2Term::const_to_string() const
{
  term_constructor_t tc = yices_term_constructor(term);
  if (tc == YICES_ARITH_CONSTANT)
  {
    string repr = yices_term_to_string(term, 120, 1, 0);
    if (repr.substr(0, 1) == "-")
    {
      // put in smt-lib format
      repr = "(- " + repr.substr(1, repr.length() - 1) + ")";
    }
    return repr;
  }
  else if (tc == YICES_BV_CONSTANT)
  {
    string repr = yices_term_to_string(term, 120, 1, 0);
    if (repr.substr(0, 2) == "0b")
    {
      repr = "#b" + repr.substr(2, repr.length() - 2);
    }
    return repr;
  }
  else
  {
    return yices_term_to_string(term, 120, 1, 0);
  }
}

// end Yices2Term implementation

}  // namespace smt
