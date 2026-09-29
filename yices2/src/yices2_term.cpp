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
#include <unordered_map>

#include "exceptions.h"
#include "ops.h"
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
    case YICES_UPDATE_TERM: return Op();
    case YICES_TUPLE_TERM: return Op();
    case YICES_FORALL_TERM: return Op();
    case YICES_LAMBDA_TERM: return Op();
    case YICES_BV_ARRAY:
      sres = const_to_string();
      sres = sres.substr(sres.find("(") + 1, sres.length());
      sres = sres.substr(0, sres.find(" "));
      if (sres == "bv-concat")
      {
        return Op(Concat);
      }
      return Op();
    case YICES_ARITH_ROOT_ATOM: return Op();
    case YICES_CEIL: return Op();
    case YICES_FLOOR: return Op();
    case YICES_IS_INT_ATOM: return Op();
    case YICES_DIVIDES_ATOM: return Op();
    // projections
    case YICES_SELECT_TERM: return Op();
    case YICES_BIT_TERM:
      // TODO: Must fix this to extract coorect bit.
      sres = const_to_string();
      sres = sres.substr(sres.find("(") + 1, sres.length());
      sres = sres.substr(0, sres.find(" "));
      if (sres == "bv-extract")
      {
        return Op(Extract);
      }
      return Op();
    // atomic terms
    case YICES_BOOL_CONSTANT: return Op();
    case YICES_ARITH_CONSTANT: return Op();
    case YICES_BV_CONSTANT: return Op();
    case YICES_SCALAR_CONSTANT: return Op();
    case YICES_VARIABLE: return Op();
    case YICES_UNINTERPRETED_TERM:
      if (yices_term_is_function(term))
      {
        if (!is_function)
        {
          return Op(Select);
        }
        return Op(Apply);
      }

      return Op();
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
  // functions are symbols
  if (is_function)
  {
    return true;
  }

  term_constructor_t tc = yices_term_constructor(term);
  return (
      (tc == YICES_UNINTERPRETED_TERM && yices_term_num_children(term) == 0));
}

bool Yices2Term::is_param() const
{
  throw NotImplementedException(
      "Yices2 backend does not support parameters yet.");
}

bool Yices2Term::is_symbolic_const() const
{
  // functions and parameters are not constants
  // don't need to check parameters because not supported yet
  if (is_function)
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

uint64_t Yices2Term::to_int() const
{
  std::string val = yices_term_to_string(term, 120, 1, 0);

  // Process bit-vector format.
  if (yices_term_is_bitvector(term))
  {
    if (val.find("0b") == std::string::npos)
    {
      std::string msg = val;
      msg += " is not a constant term, can't convert to int.";
      throw IncorrectUsageException(msg.c_str());
    }
    try
    {
      return std::stoi(val.substr(val.find("b") + 1, val.length()), 0, 2);
    }
    catch (std::exception const & e)
    {
      std::string msg("Term ");
      msg += val;
      msg += " does not contain an integer representable by a machine int.";
      throw IncorrectUsageException(msg.c_str());
    }
  }

  // If not bit-vector, try parsing an int from the term.
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
