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

#include "generic_term.h"

#include "exceptions.h"
#include "utils.h"

using namespace std;

namespace smt {

/* GenericTerm */

GenericTerm::GenericTerm(Sort s, Op o, TermVec c, string r)
    : sort(s), op(o), children(c), repr(r), is_sym(false), is_par(false)
{
  ground = compute_ground();
}

GenericTerm::GenericTerm(Sort s, Op o, TermVec c, string r, bool is_sym)
    : sort(s),
      op(o),
      children(c),
      repr(r),
      is_sym(is_sym),
      is_par(!is_sym),
      ground(true)
{
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
    shared_ptr<GenericTerm> gc = static_pointer_cast<GenericTerm>(child);
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

GenericTerm::~GenericTerm() {}

Op GenericTerm::get_op() const { return op; }

TermVec GenericTerm::get_children() { return children; }

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
  shared_ptr<GenericTerm> gt = static_pointer_cast<GenericTerm>(t);
  // The comparison is based on a string comparison
  return repr == gt->to_string();
}

string GenericTerm::compute_string() const
{
  if (!repr.empty())
  {
    return repr;
  }
  Assert(!op.is_null());
  string result = "(";
  result += op.to_string();
  for (auto c : children)
  {
    result += " " + c->to_string();
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

TermIter GenericTerm::begin()
{
  return TermIter(new GenericTermIter(children.begin()));
}

TermIter GenericTerm::end()
{
  return TermIter(new GenericTermIter(children.end()));
}

string GenericTerm::to_string()
{
  if (repr.empty())
  {
    repr = compute_string();
  }
  return repr;
}

size_t GenericTerm::hash() const { return str_hash(compute_string()); }

// check if op is null because a non-value
// may have been simplified to a value by the underlying solver
bool GenericTerm::is_value() const
{
  return op == Op() && !is_param() && !is_symbolic_const();
}

bool GenericTerm::is_ground() const { return ground; }

uint64_t GenericTerm::to_int() const { 
  Assert(repr.at(0) == '#');
  Assert(repr.at(1)  == 'b');
  std::string bit_string = repr.substr(2, repr.size() - 1);
  uint64_t result = std::stoi(bit_string, 0, 2);
  return result;
}

std::string GenericTerm::print_value_as(SortKind sk)
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

/* GenericTermIter */

GenericTermIter::GenericTermIter(TermVec::iterator i) : it(i) {}

GenericTermIter::GenericTermIter(const GenericTermIter & lit) : it(lit.it) {}

GenericTermIter::~GenericTermIter() {}

GenericTermIter & GenericTermIter::operator=(const GenericTermIter & lit)
{
  it = lit.it;
  return *this;
}

void GenericTermIter::operator++() { it++; }

const Term GenericTermIter::operator*() { return *it; }

TermIterBase * GenericTermIter::clone() const
{
  return new GenericTermIter(it);
}

bool GenericTermIter::operator==(const GenericTermIter & lit)
{
  return it == lit.it;
}

bool GenericTermIter::operator!=(const GenericTermIter & lit)
{
  return it != lit.it;
}

bool GenericTermIter::equal(const TermIterBase & other) const
{
  const GenericTermIter & lit = static_cast<const GenericTermIter &>(other);
  return it == lit.it;
}

}  // namespace smt
