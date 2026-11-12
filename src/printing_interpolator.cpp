/*!
 * \file printing_interpolator.cpp
 * \brief Interpolator that wraps another and dumps the SMT-LIB of its
 *        queries
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/printing_interpolator.h"

#include <cstddef>
#include <memory>
#include <ostream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/printing_solver.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/term.h"
#include "smt-switch/utils.h"

namespace smt {

const char * name_prefix = "smt_switch_generated_";

// The terms are built, and their declarations printed, with the wrapped
// interpolator's regular solver; everything else goes to the wrapped
// interpolator, which the options, the logic and resets have to reach.
PrintingInterpolator::PrintingInterpolator(SmtInterpolator s, std::ostream * os)
    : AbsSmtInterpolator(
          s->get_kind(),
          std::make_shared<PrintingSolver>(s->backend_solver, os)),
      wrapped_interpolator(std::move(s)),
      out_stream(os)
{
  if (get_kind() == InterpolatorKind::YICES2)
  {
    (*out_stream) << "; run with yices-smt2 --mcsat --incremental" << std::endl;
  }
  initialize();
}

PrintingInterpolator::PrintingInterpolator(SmtInterpolator s,
                                           std::ostream * os,
                                           PrintingStyleEnum /* pse */)
    : PrintingInterpolator(std::move(s), os)
{
}

// the message for an interpolator whose queries printing cannot write
static std::string no_query_syntax(InterpolatorKind itp_kind)
{
  return "A printing interpolator cannot write the queries of "
         + to_string(itp_kind);
}

Result PrintingInterpolator::compute_interpolant(const Term & A,
                                                 const Term & B,
                                                 Term & out_I) const
{
  switch (get_kind())
  {
    case InterpolatorKind::CVC5:
    case InterpolatorKind::YICES2: {
      TermVec interpolant;
      Result r = print_query({ A, B }, interpolant);
      out_I = interpolant.front();
      return r;
    }
    // both define it as the sequence interpolant of A and B
    case InterpolatorKind::BZLA:
    case InterpolatorKind::MSAT: return interpolant_from_sequence(A, B, out_I);
  }
  throw NotImplementedException(no_query_syntax(get_kind()));
}

Result PrintingInterpolator::compute_seq_interpolants(const TermVec & formulae,
                                                      TermVec & out_I) const
{
  switch (get_kind())
  {
    // Both split a sequence query into one get_interpolant query per split,
    // with sequence_from_interpolants, and keep what it reuses between
    // queries. Splitting it here the same way asks the same queries, and
    // prints each as it is asked.
    case InterpolatorKind::CVC5:
    case InterpolatorKind::YICES2:
      return sequence_from_interpolants(formulae, out_I);
    // both answer it natively
    case InterpolatorKind::BZLA:
    case InterpolatorKind::MSAT: return print_query(formulae, out_I);
  }
  throw NotImplementedException(no_query_syntax(get_kind()));
}

Result PrintingInterpolator::print_query(const TermVec & formulae,
                                         TermVec & out_I) const
{
  switch (get_kind())
  {
    case InterpolatorKind::BZLA:
    case InterpolatorKind::MSAT: {
      // Both keep each formula at a context level of its own, keep those of
      // the longest prefix the query shares with the last one unless
      // incremental is off, and push the rest. MathSAT resets its
      // environment instead of popping when it keeps none.
      bool msat = get_kind() == InterpolatorKind::MSAT;
      TermVec & asserted = record->asserted;
      std::vector<std::string> & asserted_names = record->asserted_names;
      std::size_t num_reused = 0;
      // the mode of the wrapped interpolator, which copies share
      while (wrapped_interpolator->incremental_mode
             && num_reused < asserted.size() && num_reused < formulae.size()
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
        std::string name =
            msat ? "g" + std::to_string(k + 1)
                 : name_prefix + std::to_string(record->num_names++);
        (*out_stream) << "(" << PUSH_STR << " 1)" << std::endl;
        (*out_stream) << "(" << ASSERT_STR << " (! " << formulae[k] << " :"
                      << (msat ? INTERPOLATION_GROUP_STR : NAMED_STR) << " "
                      << name << "))" << std::endl;
        asserted.push_back(formulae[k]);
        asserted_names.push_back(name);
      }
      (*out_stream) << "(" << CHECK_SAT_STR << ")" << std::endl;
      Result r =
          wrapped_interpolator->get_sequence_interpolants(formulae, out_I);
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
    case InterpolatorKind::CVC5: {
      // A get_interpolant query, printed once it is answered: cvc5 asks for
      // an interpolant of the assertions and the negation of B
      Term I;
      Result r = wrapped_interpolator->get_interpolant(
          formulae.front(), formulae.back(), I);
      out_I.push_back(I);
      (*out_stream) << "(" << PUSH_STR << " 1)" << std::endl;
      (*out_stream) << "(" << ASSERT_STR << " " << formulae.front() << ")"
                    << std::endl;
      (*out_stream) << "(" << GET_INTERPOLANT_STR << " I (not "
                    << formulae.back() << "))" << std::endl;
      (*out_stream) << "(" << POP_STR << " 1)" << std::endl;
      return r;
    }
    case InterpolatorKind::YICES2: {
      // A get_interpolant query. Yices2 refutes models of B one after
      // another, which are not seen from here, so its rounds are run here
      // through refute_model and printed as they go: a check of B that
      // finds the next model, and one of A under the shared symbols' values
      // in it, until B has none left or A does not refute one.
      const Term & A = formulae.front();
      const Term & B = formulae.back();
      SmtSolver solver_a, solver_b;
      TermVec model_interpolants;
      while (true)
      {
        TermsPairVec model;
        Term model_interpolant;
        Result r = wrapped_interpolator->refute_model(
            A, B, solver_a, solver_b, model, model_interpolant);
        for (const auto & [symbol, value] : model)
        {
          // checked before printing the round, so that it is not left half
          // printed
          if (!value)
          {
            throw NotImplementedException(
                "A printing interpolator cannot write the value of "
                + symbol->to_string()
                + " in a model of B, which has no term, such as an "
                  "algebraic number");
          }
        }
        // B, with the model interpolants of the rounds before
        (*out_stream) << "(" << PUSH_STR << " 1)" << std::endl;
        (*out_stream) << "(" << ASSERT_STR << " " << B << ")" << std::endl;
        for (const Term & t : model_interpolants)
        {
          (*out_stream) << "(" << ASSERT_STR << " " << t << ")" << std::endl;
        }
        (*out_stream) << "(" << CHECK_SAT_STR << ")" << std::endl;
        if (!model.empty())
        {
          (*out_stream) << "(" << GET_VALUE_STR << " (";
          for (std::size_t i = 0; i < model.size(); ++i)
          {
            (*out_stream) << (i > 0 ? " " : "") << model[i].first;
          }
          (*out_stream) << "))" << std::endl;
        }
        (*out_stream) << "(" << POP_STR << " 1)" << std::endl;
        // The round ended at B if B had no model left, or if B's check did
        // not decide. An unknown answer with an empty model comes from B's
        // check, or from A's when the two share no symbols, so B's check is
        // run again to tell which.
        if ((r.is_unsat() && !model_interpolant)
            || (r.is_unknown() && model.empty()
                && !solver_b->check_sat().is_sat()))
        {
          Term I;
          if (r.is_unsat())
          {
            I = model_interpolants.empty() ? make_term(true)
                : model_interpolants.size() == 1
                    ? model_interpolants[0]
                    : make_term(And, model_interpolants);
          }
          out_I.push_back(I);
          return r;
        }
        // A under the shared symbols' values in B's model, those the
        // wrapped interpolator found rather than any the script finds
        (*out_stream) << "(" << PUSH_STR << " 1)" << std::endl;
        (*out_stream) << "(" << ASSERT_STR << " " << A << ")" << std::endl;
        (*out_stream) << "(" << CHECK_SAT_ASSUMING_MODEL_STR << " (";
        for (std::size_t i = 0; i < model.size(); ++i)
        {
          (*out_stream) << (i > 0 ? " " : "") << model[i].first;
        }
        (*out_stream) << ") (";
        for (std::size_t i = 0; i < model.size(); ++i)
        {
          (*out_stream) << (i > 0 ? " " : "") << model[i].second;
        }
        (*out_stream) << "))" << std::endl;
        if (model_interpolant)
        {
          (*out_stream) << "(" << GET_UNSAT_MODEL_INTERPOLANT_STR << ")"
                        << std::endl;
        }
        (*out_stream) << "(" << POP_STR << " 1)" << std::endl;
        if (!r.is_unsat())
        {
          out_I.push_back(Term());
          return r;
        }
        model_interpolants.push_back(model_interpolant);
      }
    }
  }
  throw NotImplementedException(no_query_syntax(get_kind()));
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

// these are printed once the wrapped interpolator accepts them, so that a
// refused one is not replayed

void PrintingInterpolator::set_logic(const std::string logic)
{
  wrapped_interpolator->set_logic(logic);
  (*out_stream) << "(" << SET_LOGIC_STR << " " << logic << ")" << std::endl;
}

void PrintingInterpolator::do_set_opt(const std::string & option,
                                      const std::string & value)
{
  wrapped_interpolator->set_opt(option, value);
  (*out_stream) << "(" << SET_OPTION_STR << " :" << option << " " << value
                << ")" << std::endl;
}

void PrintingInterpolator::reset_backend_assertions()
{
  (*out_stream) << "(" << RESET_ASSERTIONS_STR << ")" << std::endl;
  wrapped_interpolator->reset_assertions();
}

void PrintingInterpolator::reset_backend()
{
  (*out_stream) << "(" << RESET_STR << ")" << std::endl;
  wrapped_interpolator->reset();
}

void PrintingInterpolator::forget_queries()
{
  record->asserted.clear();
  record->asserted_names.clear();
}

void PrintingInterpolator::initialize()
{
  if (get_kind() == InterpolatorKind::YICES2)
  {
    // printed by the regular solver, as yices-smt2 needs it for
    // get-unsat-model-interpolant
    set_opt("produce-unsat-model-interpolants", "true");
  }
}

SmtInterpolator create_printing_interpolator(
    SmtInterpolator wrapped_interpolator, std::ostream * out_stream)
{
  return std::make_shared<PrintingInterpolator>(std::move(wrapped_interpolator),
                                                out_stream);
}

SmtInterpolator create_printing_interpolator(
    SmtInterpolator wrapped_interpolator,
    std::ostream * out_stream,
    PrintingStyleEnum /* style */)
{
  return create_printing_interpolator(std::move(wrapped_interpolator),
                                      out_stream);
}

}  // namespace smt
