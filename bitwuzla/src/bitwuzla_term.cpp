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
** \brief Boolector implementation of AbsTerm
**
**
**/

// include standard version of open_memstream
// for compatability with FreeBSD / Darwin which doesn't support it natively
extern "C" {
#include "memstream.h"
}

#include "bitwuzla_term.h"

using namespace std;

namespace smt {

// TODO: add implementation for all of BzlaTermIter

// TODO: add implementation for BzlaTerm
BzlaTerm::BzlaTerm(const BitwuzlaTerm * t) : term(t) {}

BzlaTerm::~BzlaTerm() {}

std::size_t BzlaTerm::hash() const { return bitwuzla_term_hash(term); }

bool BzlaTerm::compare(const Term & absterm) const
{
  shared_ptr<BzlaTerm> bterm = static_pointer_cast<BzlaTerm>(absterm);
  // in bitwuzla, the pointers will be equivalent iff the terms are equivalent
  return term == bterm->term;
}

Op BzlaTerm::get_op() const { throw SmtException("NYI"); }

Sort BzlaTerm::get_sort() const
{
  return make_shared<BzlaSort>(bitwuzla_term_get_sort(term));
}

bool BzlaTerm::is_symbol() const
{
  // Bitwuzla handles negations differently than other solvers internally
  // so it could consider a negated term to still be a constant
  // make sure semantics match up. A negated symbol is not a constant,
  // because it has an operator: (not sym)
  // TODO handle the case above (no way to check if term is negated yet)
  return bitwuzla_term_is_const(term);
}

bool BzlaTerm::is_param() const { return bitwuzla_term_is_var(term); }

bool BzlaTerm::is_symbolic_const() const
{
  // in Bitwuzla arrays are functions
  // for smt-switch we consider arrays symbolic constants but not functions
  bool is_function =
      bitwuzla_term_is_fun(term) && !bitwuzla_term_is_array(term);
  return is_symbol() && !is_function;
}

bool BzlaTerm::is_value() const
{
  return bitwuzla_term_is_bv_value(term) || bitwuzla_term_is_const_array(term);
}

std::string BzlaTerm::to_string() { return to_string_formatted("smt2"); }

uint64_t BzlaTerm::to_int() const
{
  if (!bitwuzla_term_is_bv_value(term))
  {
    throw IncorrectUsageException(
        "Can't get bitstring from a non-bitvector value term.");
  }
  uint32_t width = bitwuzla_term_bv_get_size(term);
  if (width > 64)
  {
    string msg("Can't represent a bit-vector of size ");
    msg += std::to_string(width);
    msg += " in a uint64_t";
    throw IncorrectUsageException(msg.c_str());
  }
  string bits = to_string_formatted("btor");
  string::size_type sz = 0;
  return std::stoull(bits, &sz, 2);
}

TermIter BzlaTerm::begin() { throw SmtException("NYI"); }

TermIter BzlaTerm::end() { throw SmtException("NYI"); }

string BzlaTerm::print_value_as(SortKind sk)
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Cannot use print_value_as on a non-value term.");
  }

  if (bitwuzla_term_is_bv(term))
  {
    uint64_t width = bitwuzla_term_bv_get_size(term);
    if (width == 1 && sk == BOOL)
    {
      if (bitwuzla_term_is_bv_value_one(term))
      {
        return "true";
      }
      else
      {
        return "false";
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

// protected helpers
std::string BzlaTerm::to_string_formatted(const char * fmt) const
{
  // TODO: make sure this works all right for symbols etc...
  char * cres;
  size_t size;
  FILE * stream = open_memstream(&cres, &size);
  bitwuzla_term_dump(term, fmt, stream);
  int64_t status = fflush(stream);
  if (status != 0)
  {
    throw InternalSolverException(
        "Error flushing stream for bitwuzla to_string");
  }
  status = fclose(stream);
  if (status != 0)
  {
    throw InternalSolverException(
        "Error closing stream for bitwuzla to_string");
  }
  string sres(cres);
  free(cres);
  return sres;
}

}  // namespace smt
