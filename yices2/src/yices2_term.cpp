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

/* A term no smt-switch op describes cannot be reported as one: a null op
 * would say the term is a leaf, which whoever rebuilds it from its children
 * would believe.
 */
[[noreturn]] static void no_smt_switch_op(term_t term)
{
  char * printed = yices_term_to_string(term, 120, 1, 0);
  std::string message("No smt-switch op for the Yices2 term ");
  message += printed;
  yices_free_string(printed);
  throw NotImplementedException(message);
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
    case YICES_ARITH_FF_SUM: no_smt_switch_op(term);
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
    case YICES_TUPLE_TERM: no_smt_switch_op(term);
    case YICES_FORALL_TERM: no_smt_switch_op(term);
    case YICES_LAMBDA_TERM: no_smt_switch_op(term);
    case YICES_BV_ARRAY: {
      uint32_t low = 0;
      uint32_t high = 0;
      if (extract_argument(term, low, high) != NULL_TERM)
      {
        return Op(Extract, high, low);
      }
      // an array of Booleans otherwise, read as a concatenation of the
      // width-one vectors the iterator makes of them, split so that the two
      // children Concat takes are the top bit and the rest. One bit on its
      // own is the Ite that widens it.
      return yices_term_num_children(term) == 1 ? Op(Ite) : Op(Concat);
    }
    case YICES_ARITH_ROOT_ATOM: no_smt_switch_op(term);
    case YICES_CEIL: no_smt_switch_op(term);
    case YICES_FLOOR: return Op(To_Int);
    case YICES_IS_INT_ATOM: return Op(Is_Int);
    case YICES_DIVIDES_ATOM: no_smt_switch_op(term);
    // projections
    case YICES_SELECT_TERM: no_smt_switch_op(term);
    // a bit select is a Boolean, which no op gives for a bit-vector, so
    // it reads as that bit compared against one
    case YICES_BIT_TERM: return Op(Equal);
    // atomic terms
    case YICES_BOOL_CONSTANT: return Op();
    case YICES_ARITH_CONSTANT: return Op();
    case YICES_ARITH_FF_CONSTANT: no_smt_switch_op(term);
    case YICES_BV_CONSTANT: return Op();
    case YICES_SCALAR_CONSTANT: return Op();
    case YICES_VARIABLE: return Op();
    case YICES_UNINTERPRETED_TERM: return Op();
    // reported for a term that is not valid, which this one is
    case YICES_CONSTRUCTOR_ERROR:
      throw InternalSolverException(yices_error_string());
  }
  // unreachable, and here so that a constructor Yices adds is a -Wswitch
  // warning rather than a term silently without an op
  throw InternalSolverException("Unknown Yices2 term constructor "
                                + std::to_string(static_cast<int>(tc)));
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

/* How many children smt-switch sees, which has to agree with get_op().
 * Yices keeps a sum or a product as a polynomial, so each component becomes
 * one synthesised child. A one-component arithmetic sum or power product is
 * the exception: get_op() reads those as Mult and Pow, whose children are
 * the coefficient and the term, or the base and the exponent.
 */
static uint32_t smt_num_children(term_t term)
{
  int32_t num_children = yices_term_num_children(term);
  if (num_children <= 0)
  {
    // atoms, and anything Yices does not consider composite, have none
    return 0;
  }
  term_constructor_t tc = yices_term_constructor(term);
  if (tc == YICES_BIT_TERM)
  {
    // the Equal reading: the width-one extract, and the one it meets
    return 2;
  }
  if (yices_term_is_projection(term))
  {
    // a projection reports one child, reachable only through proj_arg
    return 1;
  }
  uint32_t low = 0;
  uint32_t high = 0;
  if (tc == YICES_BV_ARRAY)
  {
    if (extract_argument(term, low, high) != NULL_TERM)
    {
      // get_op reads this as Extract, whose one child is the bitvector
      return 1;
    }
    // the Ite reading for one bit, and otherwise the two Concat takes
    return num_children == 1 ? 3 : 2;
  }
  if (num_children == 1
      && (yices_term_is_sum(term) || yices_term_is_product(term)))
  {
    return 2;
  }
  return static_cast<uint32_t>(num_children);
}

Yices2TermIter::Yices2TermIter(term_t t, uint32_t p, bool f)
    : term(t), pos(p), is_function(f)
{
}

Yices2TermIter::Yices2TermIter(const Yices2TermIter & it)
    : term(it.term), pos(it.pos), is_function(it.is_function)
{
}

Yices2TermIter & Yices2TermIter::operator=(const Yices2TermIter & it)
{
  term = it.term;
  pos = it.pos;
  is_function = it.is_function;
  return *this;
}

void Yices2TermIter::operator++() { pos++; }

const Term Yices2TermIter::operator*()
{
  term_t ret_term;

  if (yices_term_is_bvsum(term))
  {
    // each component is a bitvector coefficient times a term, and a constant
    // summand has no term at all: then the coefficient is the value
    uint32_t width = yices_term_bitsize(term);
    std::vector<int32_t> coeff(width);
    term_t component;
    if (yices_bvsum_component(term, pos, coeff.data(), &component) < 0)
    {
      throw InternalSolverException(yices_error_string());
    }
    term_t y_coeff = yices_bvconst_from_array(width, coeff.data());
    ret_term =
        component == NULL_TERM ? y_coeff : yices_bvmul(y_coeff, component);
  }
  else if (yices_term_is_sum(term))
  {
    mpq_t coeff;
    mpq_init(coeff);
    term_t component;
    if (smt_num_children(term) == 2 && yices_term_num_children(term) == 1)
    {
      // the Mult reading: the coefficient, then the term it multiplies
      if (yices_sum_component(term, 0, coeff, &component) < 0)
      {
        mpq_clear(coeff);
        throw InternalSolverException(yices_error_string());
      }
      ret_term = pos == 0 ? yices_mpq(coeff) : component;
    }
    else
    {
      if (yices_sum_component(term, pos, coeff, &component) < 0)
      {
        mpq_clear(coeff);
        throw InternalSolverException(yices_error_string());
      }
      ret_term = component == NULL_TERM
                     ? yices_mpq(coeff)
                     : yices_mul(yices_mpq(coeff), component);
    }
    mpq_clear(coeff);
  }
  else if (yices_term_is_product(term))
  {
    term_t component;
    uint32_t exponent;
    if (yices_product_component(
            term, smt_num_children(term) == 2 ? 0 : pos, &component, &exponent)
        < 0)
    {
      throw InternalSolverException(yices_error_string());
    }
    if (smt_num_children(term) == 2 && yices_term_num_children(term) == 1)
    {
      // the Pow reading: the base, then the exponent
      ret_term = pos == 0 ? component : yices_int64(exponent);
    }
    else
    {
      // yices_power rejects an uninterpreted term, so an exponent of one is
      // the component itself rather than a power of it
      ret_term = exponent == 1 ? component : yices_power(component, exponent);
    }
  }
  else if (yices_term_constructor(term) == YICES_BIT_TERM)
  {
    // the Equal reading: ((_ extract i i) x) and then #b1
    int32_t index = yices_proj_index(term);
    ret_term = pos == 0 ? yices_bvextract(yices_proj_arg(term), index, index)
                        : yices_bvconst_one(1);
  }
  else if (yices_term_is_projection(term))
  {
    // yices_term_child rejects a projection
    ret_term = yices_proj_arg(term);
  }
  else if (yices_term_constructor(term) == YICES_BV_ARRAY)
  {
    uint32_t low = 0;
    uint32_t high = 0;
    term_t argument = extract_argument(term, low, high);
    int32_t num_bits = yices_term_num_children(term);
    if (argument != NULL_TERM)
    {
      ret_term = argument;
    }
    else if (num_bits == 1)
    {
      // the Ite reading: the Boolean, then the one and the zero it picks
      ret_term = pos == 0   ? yices_term_child(term, 0)
                 : pos == 1 ? yices_bvconst_one(1)
                            : yices_bvconst_zero(1);
    }
    else
    {
      // the Concat reading. Yices keeps the least significant bit first, so
      // the high child is the last one, and the low child is everything
      // below it, itself an array this iterator reads the same way.
      std::vector<term_t> bits(num_bits);
      for (int32_t i = 0; i < num_bits; i++)
      {
        bits[i] = yices_term_child(term, i);
      }
      ret_term = pos == 0 ? yices_bvarray(1, &bits[num_bits - 1])
                          : yices_bvarray(num_bits - 1, bits.data());
    }
  }
  else
  {
    ret_term = yices_term_child(term, pos);
  }

  if (ret_term == NULL_TERM)
  {
    throw InternalSolverException(yices_error_string());
  }
  // Only an application's first child is a function, and whether it is one
  // rather than an array is what this term's own flag says. Everything else,
  // the array a store updates included, is not a function, and asking Yices
  // would not help: it calls an array one too.
  return std::make_shared<Yices2Term>(ret_term, pos == 0 && is_function);
}

TermIterBase * Yices2TermIter::clone() const
{
  return new Yices2TermIter(term, pos, is_function);
}

bool Yices2TermIter::operator==(const Yices2TermIter & it)
{
  return term == it.term && pos == it.pos;
}

bool Yices2TermIter::operator!=(const Yices2TermIter & it)
{
  return !(*this == it);
}

bool Yices2TermIter::equal(const TermIterBase & other) const
{
  const Yices2TermIter & it = static_cast<const Yices2TermIter &>(other);
  return term == it.term && pos == it.pos;
}

TermIter Yices2Term::begin()
{
  return TermIter(new Yices2TermIter(term, 0, is_function));
}

TermIter Yices2Term::end()
{
  return TermIter(
      new Yices2TermIter(term, smt_num_children(term), is_function));
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
