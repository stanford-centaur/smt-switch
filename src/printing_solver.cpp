/*********************                                                        */
/*! \file printing_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that wraps another SmtSolver and dumps SMT-LIB
**        that corresponds to the operations being performed.
**        The SMT-LIB command is printed before being executed,
**        so that in case of an error it easier to see when it happened.
**/

#include "printing_solver.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <ostream>
#include <string>
#include <vector>

#include "exceptions.h"
#include "smt_defs.h"
#include "smtlib_strings.h"
#include "solver_enums.h"
#include "sort.h"

namespace smt {

/* PrintingSolver */

const char * name_prefix = "smt_switch_generated_";

// implementations
PrintingSolver::PrintingSolver(SmtSolver s, std::ostream * os)
    : AbsSmtSolver(s->get_solver_enum()), wrapped_solver(s), out_stream(os)
{
}

PrintingSolver::PrintingSolver(SmtSolver s,
                               std::ostream * os,
                               PrintingStyleEnum /* pse */)
    : PrintingSolver(s, os)
{
}

PrintingSolver::~PrintingSolver() {}

Term PrintingSolver::get_symbol(const std::string & name)
{
  return wrapped_solver->get_symbol(name);
}

Sort PrintingSolver::make_sort(const std::string name,
                               std::uint64_t arity) const
{
  (*out_stream) << "(" << DECLARE_SORT_STR << " " << name << " " << arity << ")"
                << std::endl;
  return wrapped_solver->make_sort(name, arity);
}

Sort PrintingSolver::make_sort(const SortKind sk) const
{
  return wrapped_solver->make_sort(sk);
}

Sort PrintingSolver::make_sort(const SortKind sk, std::uint64_t size) const
{
  return wrapped_solver->make_sort(sk, size);
}

Sort PrintingSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  return wrapped_solver->make_sort(sk, sorts);
}

Sort PrintingSolver::make_sort(const Sort & sort_con,
                               const SortVec & sorts) const
{
  return wrapped_solver->make_sort(sort_con, sorts);
}

Term PrintingSolver::make_term(bool b) const
{
  return wrapped_solver->make_term(b);
}

Term PrintingSolver::make_term(std::int64_t i, const Sort & sort) const
{
  return wrapped_solver->make_term(i, sort);
}

Term PrintingSolver::make_term(const std::string & s,
                               bool useEscSequences,
                               const Sort & sort) const
{
  return wrapped_solver->make_term(s, useEscSequences, sort);
}

Term PrintingSolver::make_term(const std::wstring & s, const Sort & sort) const
{
  return wrapped_solver->make_term(s, sort);
}

Term PrintingSolver::make_term(const std::string name,
                               const Sort & sort,
                               std::uint64_t base) const
{
  return wrapped_solver->make_term(name, sort, base);
}

Term PrintingSolver::make_term(const Term & val, const Sort & sort) const
{
  return wrapped_solver->make_term(val, sort);
}

Term PrintingSolver::make_symbol(const std::string name, const Sort & sort)
{
  SortKind sk = sort->get_sort_kind();
  std::string domain_str = "";
  std::string range_str = "";
  if (sk == FUNCTION)
  {
    for (Sort ds : sort->get_domain_sorts())
    {
      domain_str += ds->to_string() + " ";
    }
    range_str = sort->get_codomain_sort()->to_string();
  }
  else
  {
    range_str = sort->to_string();
  }
  Term sym = wrapped_solver->make_symbol(name, sort);
  std::string name_str = sym->to_string();
  (*out_stream) << "(" << DECLARE_FUN_STR << " " << name_str << " " << "("
                << domain_str << ")" << " " << range_str << ")" << std::endl;
  return sym;
}

Term PrintingSolver::make_param(const std::string name, const Sort & sort)
{
  // bound parameters are not declared -- they'll show up in the printed term
  return wrapped_solver->make_param(name, sort);
}

Term PrintingSolver::make_term(const Op op, const TermVec & terms) const
{
  return wrapped_solver->make_term(op, terms);
}

Term PrintingSolver::get_value(const Term & t) const
{
  (*out_stream) << "(" << GET_VALUE_STR << " (" << t << "))" << std::endl;
  return wrapped_solver->get_value(t);
}

void PrintingSolver::get_unsat_assumptions(UnorderedTermSet & out)
{
  (*out_stream) << "(" << GET_UNSAT_ASSUMPTIONS_STR << ")" << std::endl;
  wrapped_solver->get_unsat_assumptions(out);
}

UnorderedTermMap PrintingSolver::get_array_values(const Term & arr,
                                                  Term & out_const_base) const
{
  (*out_stream) << "(get-value (" << arr << "))" << std::endl;
  return wrapped_solver->get_array_values(arr, out_const_base);
}

void PrintingSolver::do_reset()
{
  (*out_stream) << "(" << RESET_STR << ")" << std::endl;
  wrapped_solver->reset();
}

// dispatched to underlying solver

void PrintingSolver::set_opt(const std::string option, const std::string value)
{
  wrapped_solver->set_opt(option, value);
  (*out_stream) << "(" << SET_OPTION_STR << " :" << option << " " << value
                << ")" << std::endl;
}

void PrintingSolver::set_logic(const std::string logic)
{
  (*out_stream) << "(" << SET_LOGIC_STR << " " << logic << ")" << std::endl;
  wrapped_solver->set_logic(logic);
}

void PrintingSolver::assert_formula(const Term & t)
{
  (*out_stream) << "(" << ASSERT_STR << " " << t->to_string() << ")"
                << std::endl;
  wrapped_solver->assert_formula(t);
}

Result PrintingSolver::check_sat()
{
  (*out_stream) << "(" << CHECK_SAT_STR << ")" << std::endl;
  return wrapped_solver->check_sat();
}

Result PrintingSolver::check_sat_assuming(const TermVec & assumptions)
{
  std::string assumptions_str;
  for (Term a : assumptions)
  {
    assumptions_str += a->to_string() + " ";
  }
  (*out_stream) << "(" << CHECK_SAT_ASSUMING_STR << " (" << assumptions_str
                << "))" << std::endl;
  return wrapped_solver->check_sat_assuming(assumptions);
}

void PrintingSolver::do_push(std::uint64_t num)
{
  (*out_stream) << "(" << PUSH_STR << " " << num << ")" << std::endl;
  wrapped_solver->push(num);
}

void PrintingSolver::do_pop(std::uint64_t num)
{
  (*out_stream) << "(" << POP_STR << " " << num << ")" << std::endl;
  wrapped_solver->pop(num);
}

std::uint64_t PrintingSolver::get_context_level() const
{
  return wrapped_solver->get_context_level();
}

void PrintingSolver::dump_smt2(std::string filename) const
{
  wrapped_solver->dump_smt2(filename);
}

void PrintingSolver::do_reset_assertions()
{
  (*out_stream) << "(" << RESET_ASSERTIONS_STR << ")" << std::endl;
  wrapped_solver->reset_assertions();
}

SmtSolver create_printing_solver(SmtSolver wrapped_solver,
                                 std::ostream * out_stream)
{
  return std::make_shared<PrintingSolver>(wrapped_solver, out_stream);
}

SmtSolver create_printing_solver(SmtSolver wrapped_solver,
                                 std::ostream * out_stream,
                                 PrintingStyleEnum /* style */)
{
  return create_printing_solver(wrapped_solver, out_stream);
}

/* PrintingInterpolator */

PrintingInterpolator::PrintingInterpolator(SmtInterpolator s, std::ostream * os)
    : AbsSmtInterpolator(s->get_solver_enum(),
                         std::make_shared<PrintingSolver>(s, os)),
      wrapped_interpolator(s),
      out_stream(os)
{
}

PrintingInterpolator::PrintingInterpolator(SmtInterpolator s,
                                           std::ostream * os,
                                           PrintingStyleEnum /* pse */)
    : PrintingInterpolator(s, os)
{
}

// the message for an interpolator whose queries printing cannot write
static std::string no_query_syntax(SolverEnum se)
{
  return "A printing interpolator cannot write the queries of " + to_string(se);
}

Result PrintingInterpolator::get_interpolant(const Term & A,
                                             const Term & B,
                                             Term & out_I) const
{
  TermVec interpolant;
  return print_query({ A, B }, interpolant, false, [&]() {
    Result r = wrapped_interpolator->get_interpolant(A, B, out_I);
    interpolant.push_back(out_I);
    return r;
  });
}

Result PrintingInterpolator::get_sequence_interpolants(const TermVec & formulae,
                                                       TermVec & out_I) const
{
  // check before printing, so a query that is refused is not printed
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
  return print_query(formulae, out_I, true, [&]() {
    return wrapped_interpolator->get_sequence_interpolants(formulae, out_I);
  });
}

Result PrintingInterpolator::print_query(
    const TermVec & formulae,
    const TermVec & out_I,
    bool sequence,
    const std::function<Result()> & ask) const
{
  switch (get_solver_enum())
  {
    case BZLA_INTERPOLATOR:
    case MSAT_INTERPOLATOR: {
      // Both keep each formula at a context level of its own, keep those of
      // the longest prefix the query shares with the last one unless
      // incremental is off, and push the rest. MathSAT resets its
      // environment instead of popping when it keeps none.
      bool msat = get_solver_enum() == MSAT_INTERPOLATOR;
      std::size_t num_reused = 0;
      while (incremental_mode && num_reused < asserted.size()
             && num_reused < formulae.size()
             && asserted[num_reused] == formulae[num_reused])
      {
        ++num_reused;
      }
      if (msat && num_reused == 0 && !asserted.empty())
      {
        (*out_stream) << "(" << RESET_ASSERTIONS_STR << ")" << std::endl;
      }
      else if (num_reused < asserted.size())
      {
        (*out_stream) << "(" << POP_STR << " " << asserted.size() - num_reused
                      << ")" << std::endl;
      }
      asserted.resize(num_reused);
      asserted_names.resize(num_reused);
      for (std::size_t k = num_reused; k < formulae.size(); ++k)
      {
        // a MathSAT interpolation group per level; Bitwuzla names every
        // formula, since one asserted last may be reused as a partition
        std::string name = msat ? "g" + std::to_string(k + 1)
                                : name_prefix + std::to_string(num_names++);
        (*out_stream) << "(" << PUSH_STR << " 1)" << std::endl;
        (*out_stream) << "(" << ASSERT_STR << " (! " << formulae[k] << " :"
                      << (msat ? INTERPOLATION_GROUP_STR : NAMED_STR) << " "
                      << name << "))" << std::endl;
        asserted.push_back(formulae[k]);
        asserted_names.push_back(name);
      }
      (*out_stream) << "(" << CHECK_SAT_STR << ")" << std::endl;
      Result r = ask();
      // the interpolants are asked for only after an unsat answer
      if (r.is_unsat() && msat)
      {
        // one per prefix of the groups
        for (std::size_t i = 1; i < formulae.size(); ++i)
        {
          (*out_stream) << "(" << GET_INTERPOLANT_STR << " (";
          for (std::size_t j = 0; j < i; ++j)
          {
            (*out_stream) << (j > 0 ? " " : "") << asserted_names[j];
          }
          (*out_stream) << "))" << std::endl;
        }
      }
      else if (r.is_unsat())
      {
        // all at once, partitioned into every formula but the last
        (*out_stream) << "(" << GET_INTERPOLANTS_STR;
        for (std::size_t j = 0; j + 1 < formulae.size(); ++j)
        {
          (*out_stream) << " (" << asserted_names[j] << ")";
        }
        (*out_stream) << ")" << std::endl;
      }
      return r;
    }
    case CVC5_INTERPOLATOR: {
      // cvc5 has no sequence query, so a sequence query asks one query per
      // split, from the interpolant of the split before, as
      // sequence_from_interpolants does; they are printed once those
      // interpolants are known. It reuses the interpolants of an unsat last
      // sequence query that this one extends, unless incremental is off,
      // and asks no more after a split that fails. A get_interpolant query
      // is asked on its own and leaves the last sequence query as it was.
      std::size_t first_split = 0;
      if (sequence && incremental_mode && !last_unsat_query.empty()
          && last_unsat_query.size() <= formulae.size()
          && std::equal(last_unsat_query.begin(),
                        last_unsat_query.end(),
                        formulae.begin()))
      {
        first_split = last_unsat_query.size() - 1;
      }
      Result r = ask();
      if (sequence)
      {
        last_unsat_query = r.is_unsat() ? formulae : TermVec();
      }
      for (std::size_t i = first_split; i < out_I.size(); ++i)
      {
        if (i > 0 && !out_I[i - 1])
        {
          break;
        }
        (*out_stream) << "(" << PUSH_STR << " 1)" << std::endl;
        // the split asserts the conjunction of the interpolant before it
        // and its formula
        (*out_stream) << "(" << ASSERT_STR << " ";
        if (i > 0)
        {
          (*out_stream) << "(and " << out_I[i - 1] << " " << formulae[i] << ")";
        }
        else
        {
          (*out_stream) << formulae[i];
        }
        (*out_stream) << ")" << std::endl;
        (*out_stream) << "(" << GET_INTERPOLANT_STR << " I (not ";
        if (i + 2 == formulae.size())
        {
          (*out_stream) << formulae.back();
        }
        else
        {
          (*out_stream) << "(and";
          for (std::size_t j = i + 1; j < formulae.size(); ++j)
          {
            (*out_stream) << " " << formulae[j];
          }
          (*out_stream) << ")";
        }
        (*out_stream) << "))" << std::endl;
        (*out_stream) << "(" << POP_STR << " 1)" << std::endl;
      }
      return r;
    }
    case BTOR:
    case BZLA:
    case CVC5:
    case GENERIC_SOLVER:
    case MSAT:
    case YICES2:
    case Z3: break;
  }
  throw NotImplementedException(no_query_syntax(get_solver_enum()));
}

void PrintingInterpolator::set_opt(const std::string option,
                                   const std::string value)
{
  if (option == "incremental")
  {
    // every interpolator takes it for itself, to decide whether a query
    // reuses what it shares with the last one, and none passes it on to
    // its solver, so it goes straight to the wrapped interpolator and is
    // not printed
    wrapped_interpolator->set_opt(option, value);
  }
  AbsSmtInterpolator::set_opt(option, value);
}

void PrintingInterpolator::do_set_opt(const std::string & option,
                                      const std::string & value)
{
  backend_solver->set_opt(option, value);
}

void PrintingInterpolator::forget_queries()
{
  asserted.clear();
  asserted_names.clear();
  last_unsat_query.clear();
}

SmtInterpolator create_printing_interpolator(
    SmtInterpolator wrapped_interpolator, std::ostream * out_stream)
{
  return std::make_shared<PrintingInterpolator>(wrapped_interpolator,
                                                out_stream);
}

SmtInterpolator create_printing_interpolator(
    SmtInterpolator wrapped_interpolator,
    std::ostream * out_stream,
    PrintingStyleEnum /* style */)
{
  return create_printing_interpolator(wrapped_interpolator, out_stream);
}

}  // namespace smt
