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
BzlaTerm::BzlaTerm(Bitwuzla * b, BitwuzlaTerm * t) : bzla(b), term(t) {}

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
  return make_shared<BzlaSort>(bzla, bitwuzla_term_get_sort(bzla, term));
}

bool BzlaTerm::is_symbol() const { throw SmtException("NYI"); }

bool BzlaTerm::is_param() const { throw SmtException("NYI"); }

bool BzlaTerm::is_symbolic_const() const { throw SmtException("NYI"); }

bool BzlaTerm::is_value() const { throw SmtException("NYI"); }

std::string BzlaTerm::to_string() { return to_string_formatted("smt2"); }

uint64_t BzlaTerm::to_int() const
{
  if (!bitwuzla_term_is_bv_value(bzla, term))
  {
    throw IncorrectUsageException(
        "Can't get bitstring from a non-bitvector value term.");
  }
  std::string bits = to_string_formatted("btor");
  uint32_t width = bitwuzla_term_bv_get_size(term);
  if (width > 64)
  {
    std::string msg("Can't represent a bit-vector of size ");
    msg += std::to_string(width);
    msg += " in a uint64_t";
    throw IncorrectUsageException(msg.c_str());
  }
  std::string::size_type sz = 0;
  return std::stoull(s, &sz, 2);
}

TermIter BzlaTerm::begin() { throw SmtException("NYI"); }

TermIter BzlaTerm::end() { throw SmtException("NYI"); }

// protected helpers
std::string to_string_formatted(const char * fmt) const
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
  sres = cres;
  free(cres);
  return sres;
}

}  // namespace smt
