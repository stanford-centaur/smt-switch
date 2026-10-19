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

#include <algorithm>
#include <cassert>
#include <utility>

#include "exceptions.h"
#include "ops.h"

namespace smt {

AbsSmtInterpolator::AbsSmtInterpolator(SolverEnum se, SmtSolver backend_solver)
    : AbsSmtSolver(se), backend_solver(std::move(backend_solver))
{
}

// ------------------------- Forbidden ---------------------------------------

void AbsSmtInterpolator::do_push(std::uint64_t /* num */)
{
  throw IncorrectUsageException("Can't call push from interpolating solver");
}

void AbsSmtInterpolator::do_pop(std::uint64_t /* num */)
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

UnorderedTermMap AbsSmtInterpolator::get_array_values(
    const Term & /* arr */, Term & /* out_const_base */) const
{
  throw IncorrectUsageException(
      "Can't get array values from interpolating solver");
}

void AbsSmtInterpolator::get_unsat_assumptions(UnorderedTermSet & /* out */)
{
  throw IncorrectUsageException(
      "Can't get unsat assumptions from interpolating solver");
}

void AbsSmtInterpolator::dump_smt2(std::string /* filename */) const
{
  throw IncorrectUsageException(
      "Can't dump assertions from interpolating solver, which holds none");
}

std::uint64_t AbsSmtInterpolator::get_context_level() const { return 0; }

// ------------------------- Handled here ------------------------------------

void AbsSmtInterpolator::set_opt(const std::string option,
                                 const std::string value)
{
  if (option != "incremental")
  {
    do_set_opt(option, value);
    return;
  }
  // no interpolator passes it on to its regular solver
  if (value == "true")
  {
    incremental_mode = true;
  }
  else if (value == "false")
  {
    incremental_mode = false;
  }
  else
  {
    throw IncorrectUsageException(
        "Invalid value for boolean option 'incremental'");
  }
}

void AbsSmtInterpolator::do_reset_assertions()
{
  last_itp_query_formulae.clear();
  last_itp_query_interpolants.clear();
  forget_queries();
  backend_solver->reset_assertions();
}

void AbsSmtInterpolator::do_reset()
{
  // first, as what is kept can be terms that the reset destroys
  last_itp_query_formulae.clear();
  last_itp_query_interpolants.clear();
  forget_queries();
  backend_solver->reset();
  incremental_mode = true;
  initialize();
}

void AbsSmtInterpolator::forget_queries() {}

void AbsSmtInterpolator::initialize() {}

// ------------------------- Forwarded ---------------------------------------

void AbsSmtInterpolator::set_logic(const std::string logic)
{
  backend_solver->set_logic(logic);
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
  if (formulae.size() < 2)
  {
    throw IncorrectUsageException(
        "Sequence interpolation requires at least 2 formulae.");
  }
  if (!out_I.empty())
  {
    throw IncorrectUsageException(
        "Argument out_I should be empty before calling "
        "get_sequence_interpolants.");
  }
  for (const Term & f : formulae)
  {
    if (f->get_sort()->get_sort_kind() != BOOL)
    {
      throw IncorrectUsageException(
          "get_sequence_interpolants requires boolean terms");
    }
  }

  if (!incremental_mode)
  {
    last_itp_query_formulae.clear();
    last_itp_query_interpolants.clear();
  }

  // A query that starts with all of an unsat last one only strengthens the
  // B side of the splits they share, so their interpolants still hold, and
  // the chain goes on from the last of them.
  std::size_t first_split = 0;
  std::size_t last_size = last_itp_query_formulae.size();
  if (!last_itp_query_interpolants.empty() && last_size <= formulae.size()
      && std::equal(last_itp_query_formulae.begin(),
                    last_itp_query_formulae.end(),
                    formulae.begin()))
  {
    out_I = last_itp_query_interpolants;
    first_split = last_size - 1;
  }

  // a split after a failed one has no interpolant to start from, so it
  // fails too
  bool any_fails = false;
  for (std::size_t i = first_split; i + 1 < formulae.size(); ++i)
  {
    if (any_fails)
    {
      out_I.push_back(Term());
      continue;
    }
    TermVec rest(formulae.begin() + i + 1, formulae.end());
    Term B = rest.size() == 1 ? rest.front() : make_term(And, rest);
    Term A = i == 0 ? formulae[i] : make_term(And, out_I[i - 1], formulae[i]);
    Term I;
    Result r = get_interpolant(A, B, I);
    // only the first split can be satisfiable: each later one is unsat by
    // the interpolant before it
    if (i == 0 && r.is_sat())
    {
      last_itp_query_formulae.clear();
      last_itp_query_interpolants.clear();
      return r;
    }
    if (!r.is_unsat() || !I)
    {
      any_fails = true;
      out_I.push_back(Term());
    }
    else
    {
      out_I.push_back(I);
    }
  }

  if (any_fails)
  {
    last_itp_query_formulae.clear();
    last_itp_query_interpolants.clear();
    return Result(
        UNKNOWN,
        "Had at least one interpolation failure in get_sequence_interpolants");
  }
  last_itp_query_formulae = formulae;
  last_itp_query_interpolants = out_I;
  return Result(UNSAT);
}

}  // namespace smt
