/*********************                                                        */
/*! \file generic_term.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that maintains the expected
**        Op and children
**
**/

#include "smt-switch/generic_term.h"

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/generic_sort.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/utils.h"

namespace smt {

/* GenericTerm */

GenericTerm::GenericTerm(Sort s, Op o, TermVec c, std::string r)
    : sort(std::move(s)),
      op(o),
      children(c.empty() ? nullptr
                         : std::make_shared<const TermVec>(std::move(c))),
      repr(std::move(r))
{
  if (repr.empty() && op.is_null())
  {
    throw IncorrectUsageException(
        "A generic term needs an operator or a representation");
  }
  ground = compute_ground();
}

GenericTerm::GenericTerm(Sort s, Op o, TermVec c, std::string r, bool symbol)
    : sort(std::move(s)),
      op(o),
      children(c.empty() ? nullptr
                         : std::make_shared<const TermVec>(std::move(c))),
      repr(std::move(r)),
      is_sym(symbol),
      is_par(!symbol)
{
  if (repr.empty() && op.is_null())
  {
    throw IncorrectUsageException(
        "A generic term needs an operator or a representation");
  }
  ground = compute_ground();
}

bool GenericTerm::compute_ground()
{
  // parameters are not ground terms
  if (is_param())
  {
    return false;
  }
  // if one of the children is not ground, then the term
  // is not ground.
  for (Term child : get_children())
  {
    std::shared_ptr<GenericTerm> gc =
        std::static_pointer_cast<GenericTerm>(child);
    // This is not a recursive call -- is_ground is
    // just a getter. Their `ground` member
    // was initialized upon their construction.
    if (!gc->is_ground())
    {
      return false;
    }
  }
  return true;
}

Op GenericTerm::get_op() const { return op; }

TermVec GenericTerm::get_children() const
{
  return children ? *children : TermVec{};
}

Sort GenericTerm::get_sort() const { return sort; }

std::size_t GenericTerm::get_id() const { return hash(); }

bool GenericTerm::compare(const Term & t) const
{
  // TODO: not efficient. Should do similar to logging term.
  // the difference is that there is no underlying solver,
  // and that we need some string sometimes anyway to create a
  // generic term.
  if (!t)
  {
    // The null term is different than any constructed term.
    return false;
  }
  std::shared_ptr<GenericTerm> gt = std::dynamic_pointer_cast<GenericTerm>(t);
  // The comparison is based on a string comparison. A param is not the
  // term printed like it, since the binary is given it under a name of its
  // own.
  return gt && is_par == gt->is_par && repr == gt->to_string();
}

std::string GenericTerm::compute_string() const
{
  if (!repr.empty())
  {
    return repr;
  }
  std::string result = "(";
  result += op.to_string();
  if (children)
  {
    for (auto c : *children)
    {
      result += " " + c->to_string();
    }
  }
  result += ")";
  return result;
}

bool GenericTerm::is_symbol() const
{
  // functions, parameters, and symbolic constants are all symbols
  return is_sym || is_par;
}

bool GenericTerm::is_param() const { return op.is_null() && is_par; }

bool GenericTerm::is_symbolic_const() const
{
  return is_sym && sort->get_sort_kind() != FUNCTION;
}

std::size_t GenericTerm::get_num_children() const
{
  return children ? children->size() : 0;
}

Term GenericTerm::get_child(std::size_t i) const { return (*children)[i]; }

std::string GenericTerm::to_string() const
{
  if (repr.empty())
  {
    repr = compute_string();
  }
  return repr;
}

std::size_t GenericTerm::hash() const { return str_hash(compute_string()); }

// check if op is null because a non-value
// may have been simplified to a value by the underlying solver
bool GenericTerm::is_value() const
{
  if (op.prim_op == Apply_Constructor)
  {
    // The first child is the constructor itself.
    for (std::size_t i = 1; i < children->size(); ++i)
    {
      if (!(*children)[i]->is_value())
      {
        return false;
      }
    }
    return true;
  }
  if (!op.is_null() || is_symbol())
  {
    return false;
  }
  // A datatype's constructor, selector or tester is a leaf, not a value.
  SortKind sk = sort->get_sort_kind();
  return sk != CONSTRUCTOR && sk != SELECTOR && sk != TESTER;
}

bool GenericTerm::is_ground() const { return ground; }

/** Returns the kind of a term's sort if to_int can handle it */
static SortKind int_convertible_sort_kind(const GenericTerm & term,
                                          const std::string & repr)
{
  SortKind sk = term.get_sort()->get_sort_kind();
  if (!term.is_value() || (sk != BV && sk != INT && sk != REAL))
  {
    throw IncorrectUsageException(
        "Can't convert " + repr
        + " to an integer: it is not a bit-vector or arithmetic value");
  }
  return sk;
}

std::string GenericTerm::get_constructor_name() const
{
  SortKind sk = sort->get_sort_kind();
  if (sk != CONSTRUCTOR && sk != TESTER)
  {
    throw IncorrectUsageException(
        "Only a constructor or a tester has a constructor name");
  }
  return std::static_pointer_cast<DatatypeComponentSort>(sort)->get_name();
}

std::string GenericTerm::get_param_name() const
{
  if (!is_param())
  {
    throw IncorrectUsageException("Only a param has a param name");
  }
  return smtlib_unquote_symbol(repr);
}

std::string GenericTerm::get_selector_name() const
{
  if (sort->get_sort_kind() != SELECTOR)
  {
    throw IncorrectUsageException("Only a selector has a selector name");
  }
  return std::static_pointer_cast<DatatypeComponentSort>(sort)->get_name();
}

std::string GenericTerm::get_symbol_name() const
{
  if (!is_sym)
  {
    throw IncorrectUsageException(
        "Only a symbol that is not a param has a symbol name");
  }
  // The name was quoted with smtlib_quote_symbol, which adds bars to any
  // name with a bar in it, so bars around it are always ones it added.
  return smtlib_unquote_symbol(repr);
}

std::uint64_t GenericTerm::to_int() const
{
  return int_convertible_sort_kind(*this, repr) == BV
             ? smtlib_bv_to_uint64(repr)
             : smtlib_int_to_uint64(repr);
}

std::int64_t GenericTerm::to_signed_int() const
{
  return int_convertible_sort_kind(*this, repr) == BV
             ? smtlib_bv_to_int64(repr)
             : smtlib_int_to_int64(repr);
}

std::string GenericTerm::print_value_as(SortKind /* sk */) const
{
  if (is_value())
  {
    return to_string();
  }
  else
  {
    throw IncorrectUsageException(
        "print_value_as is only applicable for values");
  }
}

}  // namespace smt
