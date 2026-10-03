/*********************                                                        */
/*! \file interpolating_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Áron Ricardo Perez-Lopez
** This file is part of the smt-switch project.
** Copyright (c) 2026 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Abstract interface for interpolating solvers.
**
**
**/

#include "interpolating_solver.h"

#include <cassert>
#include <cstddef>
#include <utility>

#include "exceptions.h"
#include "ops.h"

namespace smt {

AbsSmtInterpolator::AbsSmtInterpolator(SolverEnum se, SmtSolver backend_solver)
    : AbsSmtSolver(se), backend_solver(std::move(backend_solver))
{
}

// ------------------------- Forbidden ---------------------------------------

void AbsSmtInterpolator::push(std::uint64_t /* num */)
{
  throw IncorrectUsageException("Can't call push from interpolating solver");
}

void AbsSmtInterpolator::pop(std::uint64_t /* num */)
{
  throw IncorrectUsageException("Can't call pop from interpolating solver");
}

void AbsSmtInterpolator::assert_formula(const Term & /* t */)
{
  throw IncorrectUsageException(
      "Can't assert formulas in interpolating solver");
}

Result AbsSmtInterpolator::check_sat()
{
  throw IncorrectUsageException(
      "Can't call check_sat from interpolating solver");
}

Result AbsSmtInterpolator::check_sat_assuming(const TermVec & /* assumptions */)
{
  throw IncorrectUsageException(
      "Can't call check_sat_assuming from interpolating solver");
}

Term AbsSmtInterpolator::get_value(const Term & /* t */) const
{
  throw IncorrectUsageException("Can't get values from interpolating solver");
}

// ------------------------- Optional ----------------------------------------

void AbsSmtInterpolator::set_opt(const std::string /* option */,
                                 const std::string /* value */)
{
  throw NotImplementedException("Setting options is not supported by "
                                + to_string(solver_enum));
}

void AbsSmtInterpolator::reset()
{
  throw NotImplementedException("Resetting is not supported by "
                                + to_string(solver_enum));
}

void AbsSmtInterpolator::reset_assertions()
{
  throw NotImplementedException("Resetting assertions is not supported by "
                                + to_string(solver_enum));
}

// ------------------------- Forwarded ---------------------------------------

void AbsSmtInterpolator::set_logic(const std::string logic)
{
  backend_solver->set_logic(logic);
}

std::uint64_t AbsSmtInterpolator::get_context_level() const
{
  return backend_solver->get_context_level();
}

UnorderedTermMap AbsSmtInterpolator::get_array_values(
    const Term & arr, Term & out_const_base) const
{
  return backend_solver->get_array_values(arr, out_const_base);
}

void AbsSmtInterpolator::get_unsat_assumptions(UnorderedTermSet & out)
{
  backend_solver->get_unsat_assumptions(out);
}

Sort AbsSmtInterpolator::make_sort(const std::string name,
                                   std::uint64_t arity) const
{
  return backend_solver->make_sort(name, arity);
}

Sort AbsSmtInterpolator::make_sort(const SortKind sk) const
{
  return backend_solver->make_sort(sk);
}

Sort AbsSmtInterpolator::make_sort(const SortKind sk, std::uint64_t size) const
{
  return backend_solver->make_sort(sk, size);
}

Sort AbsSmtInterpolator::make_sort(const SortKind sk,
                                   const SortVec & sorts) const
{
  return backend_solver->make_sort(sk, sorts);
}

Sort AbsSmtInterpolator::make_sort(const Sort & sort_con,
                                   const SortVec & sorts) const
{
  return backend_solver->make_sort(sort_con, sorts);
}

Term AbsSmtInterpolator::make_term(bool b) const
{
  return backend_solver->make_term(b);
}

Term AbsSmtInterpolator::make_term(std::int64_t i, const Sort & sort) const
{
  return backend_solver->make_term(i, sort);
}

Term AbsSmtInterpolator::make_term(const std::string val,
                                   const Sort & sort,
                                   std::uint64_t base) const
{
  return backend_solver->make_term(val, sort, base);
}

Term AbsSmtInterpolator::make_term(const Term & val, const Sort & sort) const
{
  return backend_solver->make_term(val, sort);
}

Term AbsSmtInterpolator::make_symbol(const std::string name, const Sort & sort)
{
  return backend_solver->make_symbol(name, sort);
}

Term AbsSmtInterpolator::get_symbol(const std::string & name)
{
  return backend_solver->get_symbol(name);
}

Term AbsSmtInterpolator::make_param(const std::string name, const Sort & sort)
{
  return backend_solver->make_param(name, sort);
}

Term AbsSmtInterpolator::make_term(const Op op, const Term & t) const
{
  return backend_solver->make_term(op, t);
}

Term AbsSmtInterpolator::make_term(const Op op,
                                   const Term & t0,
                                   const Term & t1) const
{
  return backend_solver->make_term(op, t0, t1);
}

Term AbsSmtInterpolator::make_term(const Op op,
                                   const Term & t0,
                                   const Term & t1,
                                   const Term & t2) const
{
  return backend_solver->make_term(op, t0, t1, t2);
}

Term AbsSmtInterpolator::make_term(const Op op, const TermVec & terms) const
{
  return backend_solver->make_term(op, terms);
}

Term AbsSmtInterpolator::make_term(const std::string & s,
                                   bool useEscSequences,
                                   const Sort & sort) const
{
  return backend_solver->make_term(s, useEscSequences, sort);
}

Term AbsSmtInterpolator::make_term(const std::wstring & s,
                                   const Sort & sort) const
{
  return backend_solver->make_term(s, sort);
}

Sort AbsSmtInterpolator::make_sort(const DatatypeDecl & d) const
{
  return backend_solver->make_sort(d);
}

DatatypeDecl AbsSmtInterpolator::make_datatype_decl(const std::string & s)
{
  return backend_solver->make_datatype_decl(s);
}

DatatypeConstructorDecl AbsSmtInterpolator::make_datatype_constructor_decl(
    const std::string s)
{
  return backend_solver->make_datatype_constructor_decl(s);
}

void AbsSmtInterpolator::add_constructor(
    DatatypeDecl & dt, const DatatypeConstructorDecl & con) const
{
  backend_solver->add_constructor(dt, con);
}

void AbsSmtInterpolator::add_selector(DatatypeConstructorDecl & dt,
                                      const std::string & name,
                                      const Sort & s) const
{
  backend_solver->add_selector(dt, name, s);
}

void AbsSmtInterpolator::add_selector_self(DatatypeConstructorDecl & dt,
                                           const std::string & name) const
{
  backend_solver->add_selector_self(dt, name);
}

Term AbsSmtInterpolator::get_constructor(const Sort & s, std::string name) const
{
  return backend_solver->get_constructor(s, name);
}

Term AbsSmtInterpolator::get_tester(const Sort & s, std::string name) const
{
  return backend_solver->get_tester(s, name);
}

Term AbsSmtInterpolator::get_selector(const Sort & s,
                                      std::string con,
                                      std::string name) const
{
  return backend_solver->get_selector(s, con, name);
}

SortVec AbsSmtInterpolator::make_datatype_sorts(
    const std::vector<DatatypeDecl> & decls) const
{
  return backend_solver->make_datatype_sorts(decls);
}

Term AbsSmtInterpolator::substitute(
    const Term term, const UnorderedTermMap & substitution_map) const
{
  return backend_solver->substitute(term, substitution_map);
}

TermVec AbsSmtInterpolator::substitute_terms(
    const TermVec & terms, const UnorderedTermMap & substitution_map) const
{
  return backend_solver->substitute_terms(terms, substitution_map);
}

void AbsSmtInterpolator::dump_smt2(std::string filename) const
{
  backend_solver->dump_smt2(filename);
}

// ------------------------- Helpers -----------------------------------------

Result AbsSmtInterpolator::interpolant_from_sequence(const Term & A,
                                                     const Term & B,
                                                     Term & out_I) const
{
  TermVec formulas{ A, B };
  TermVec itp_seq;
  Result res = get_sequence_interpolants(formulas, itp_seq);
  assert(itp_seq.size() <= 1);
  if (itp_seq.size() == 1)
  {
    out_I = itp_seq.front();
  }
  return res;
}

Result AbsSmtInterpolator::sequence_from_interpolants(const TermVec & formulae,
                                                      TermVec & out_I) const
{
  // The backend computes the proof afresh for each partition, so this is
  // likely much slower than a backend's native sequence interpolation.
  std::size_t formulae_size = formulae.size();
  if (formulae_size < 2)
  {
    throw IncorrectUsageException(
        "Require at least 2 input formulae for sequence interpolation.");
  }
  if (!out_I.empty())
  {
    throw IncorrectUsageException(
        "Argument out_I should be empty before calling "
        "get_sequence_interpolants.");
  }

  Term A = formulae.at(0);
  TermVec Bvec;
  Bvec.reserve(formulae_size - 1);
  // add to Bvec in reverse order so we can pop_back later
  for (int i = formulae_size - 1; i >= 1; --i)
  {
    Bvec.push_back(formulae[i]);
  }

  // create an interpolant for each partition
  bool any_fails = false;
  while (Bvec.size())
  {
    Term B = make_term(true);
    for (auto tt : Bvec)
    {
      B = make_term(And, B, tt);
    }
    Term I;
    Result r = get_interpolant(A, B, I);
    if (!r.is_unsat())
    {
      any_fails = true;
    }
    // if unsat then interpolation didn't fail
    // and interpolant should be non-null
    assert(!r.is_unsat() || I != nullptr);
    out_I.push_back(I);
    // move formula to A and remove from Bvec
    // recall they were added to Bvec in reverse order
    A = make_term(And, A, Bvec.back());
    Bvec.pop_back();
  }

  assert(out_I.size() == formulae.size() - 1);

  if (any_fails)
  {
    return Result(
        UNKNOWN,
        "Had at least one interpolation failure in get_sequence_interpolants");
  }
  else
  {
    // created all the interpolants
    return Result(UNSAT);
  }
}

}  // namespace smt
