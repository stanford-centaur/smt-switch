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

#include <cstddef>
#include <cstdint>
#include <memory>
#include <ostream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "datatype.h"
#include "exceptions.h"
#include "ops.h"
#include "smt_defs.h"
#include "solver_enums.h"
#include "sort.h"
#include "utils.h"

namespace smt {

namespace {

/** A selector as declared: its name, and its sort, which is null for one
 *  declared with add_selector_self */
struct PrintingSelectorDecl
{
  std::string name;
  Sort sort;
};

/** A constructor declaration of the wrapped solver, with what it declares,
 *  which the wrapped declaration cannot be asked for */
class PrintingDatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  PrintingDatatypeConstructorDecl(DatatypeConstructorDecl wrapped,
                                  std::string n);
  std::string get_name() const override;
  std::size_t hash() const override;
  bool compare(const DatatypeConstructorDecl & d) const override;
  bool less(const DatatypeConstructorDecl & d) const override;

  DatatypeConstructorDecl wrapped_decl;
  std::string name;
  std::vector<PrintingSelectorDecl> selectors;
};

/** A datatype declaration of the wrapped solver, with its constructors */
class PrintingDatatypeDecl : public AbsDatatypeDecl
{
 public:
  PrintingDatatypeDecl(DatatypeDecl wrapped, std::string n);
  std::string get_name() const override;

  DatatypeDecl wrapped_decl;
  std::string name;
  std::vector<std::shared_ptr<PrintingDatatypeConstructorDecl>> constructors;
};

PrintingDatatypeConstructorDecl::PrintingDatatypeConstructorDecl(
    DatatypeConstructorDecl wrapped, std::string n)
    : wrapped_decl(std::move(wrapped)), name(std::move(n))
{
}

std::string PrintingDatatypeConstructorDecl::get_name() const { return name; }

std::size_t PrintingDatatypeConstructorDecl::hash() const
{
  return std::hash<DatatypeConstructorDecl>{}(wrapped_decl);
}

bool PrintingDatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<PrintingDatatypeConstructorDecl> other =
      std::dynamic_pointer_cast<PrintingDatatypeConstructorDecl>(d);
  return other && wrapped_decl == other->wrapped_decl;
}

bool PrintingDatatypeConstructorDecl::less(
    const DatatypeConstructorDecl & d) const
{
  return wrapped_decl < backend_pointer_cast<PrintingDatatypeConstructorDecl>(d)
                            ->wrapped_decl;
}

PrintingDatatypeDecl::PrintingDatatypeDecl(DatatypeDecl wrapped, std::string n)
    : wrapped_decl(std::move(wrapped)), name(std::move(n))
{
}

std::string PrintingDatatypeDecl::get_name() const { return name; }

/** The constructor declarations of a datatype in SMT-LIB, e.g.
 *  ((nil) (cons (head Int) (tail list))) */
std::string constructors_to_smtlib(const PrintingDatatypeDecl & d)
{
  std::string res = "(";
  for (const std::shared_ptr<PrintingDatatypeConstructorDecl> & con :
       d.constructors)
  {
    res += (res.size() > 1 ? " (" : "(") + con->name;
    for (const PrintingSelectorDecl & sel : con->selectors)
    {
      res += " (" + sel.name + " " + (sel.sort ? sel.sort->to_string() : d.name)
             + ")";
    }
    res += ")";
  }
  return res + ")";
}

}  // namespace

/* PrintingSolver */

const char * name_prefix = "smt_switch_generated_";

// implementations
PrintingSolver::PrintingSolver(SmtSolver s, std::ostream * os)
    : AbsSmtSolver(s->get_solver_enum()),
      wrapped_solver(std::move(s)),
      out_stream(os)
{
}

PrintingSolver::PrintingSolver(SmtSolver s,
                               std::ostream * os,
                               PrintingStyleEnum /* pse */)
    : PrintingSolver(std::move(s), os)
{
}

Term PrintingSolver::get_symbol(const std::string & name) const
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

Sort PrintingSolver::make_sort(const DatatypeDecl & d) const
{
  std::shared_ptr<PrintingDatatypeDecl> pd =
      backend_pointer_cast<PrintingDatatypeDecl>(d);
  Sort res = wrapped_solver->make_sort(pd->wrapped_decl);
  (*out_stream) << "(" << DECLARE_DATATYPE_STR << " ((" << pd->name << " 0)) ("
                << constructors_to_smtlib(*pd) << "))" << std::endl;
  return res;
}

SortVec PrintingSolver::make_datatype_sorts(
    const std::vector<DatatypeDecl> & decls) const
{
  std::vector<DatatypeDecl> wrapped_decls;
  wrapped_decls.reserve(decls.size());
  std::string names;
  std::string constructors;
  for (const DatatypeDecl & d : decls)
  {
    std::shared_ptr<PrintingDatatypeDecl> pd =
        backend_pointer_cast<PrintingDatatypeDecl>(d);
    wrapped_decls.push_back(pd->wrapped_decl);
    names += (names.empty() ? "(" : " (") + pd->name + " 0)";
    constructors +=
        (constructors.empty() ? "" : " ") + constructors_to_smtlib(*pd);
  }
  SortVec res = wrapped_solver->make_datatype_sorts(wrapped_decls);
  (*out_stream) << "(" << DECLARE_DATATYPE_STR << " (" << names << ") ("
                << constructors << "))" << std::endl;
  return res;
}

DatatypeDecl PrintingSolver::make_datatype_decl(const std::string & s) const
{
  return std::make_shared<PrintingDatatypeDecl>(
      wrapped_solver->make_datatype_decl(s), s);
}

DatatypeConstructorDecl PrintingSolver::make_datatype_constructor_decl(
    const std::string s) const
{
  return std::make_shared<PrintingDatatypeConstructorDecl>(
      wrapped_solver->make_datatype_constructor_decl(s), s);
}

void PrintingSolver::add_constructor(DatatypeDecl & dt,
                                     const DatatypeConstructorDecl & con) const
{
  std::shared_ptr<PrintingDatatypeDecl> pdt =
      backend_pointer_cast<PrintingDatatypeDecl>(dt);
  std::shared_ptr<PrintingDatatypeConstructorDecl> pcon =
      backend_pointer_cast<PrintingDatatypeConstructorDecl>(con);
  wrapped_solver->add_constructor(pdt->wrapped_decl, pcon->wrapped_decl);
  pdt->constructors.push_back(pcon);
}

void PrintingSolver::add_selector(DatatypeConstructorDecl & dt,
                                  const std::string & name,
                                  const Sort & s) const
{
  std::shared_ptr<PrintingDatatypeConstructorDecl> pcon =
      backend_pointer_cast<PrintingDatatypeConstructorDecl>(dt);
  wrapped_solver->add_selector(pcon->wrapped_decl, name, s);
  pcon->selectors.push_back({ name, s });
}

void PrintingSolver::add_selector_self(DatatypeConstructorDecl & dt,
                                       const std::string & name) const
{
  std::shared_ptr<PrintingDatatypeConstructorDecl> pcon =
      backend_pointer_cast<PrintingDatatypeConstructorDecl>(dt);
  wrapped_solver->add_selector_self(pcon->wrapped_decl, name);
  pcon->selectors.push_back({ name, nullptr });
}

Term PrintingSolver::get_constructor(const Sort & s, std::string name) const
{
  return wrapped_solver->get_constructor(s, name);
}

Term PrintingSolver::get_tester(const Sort & s, std::string name) const
{
  return wrapped_solver->get_tester(s, name);
}

Term PrintingSolver::get_selector(const Sort & s,
                                  std::string con,
                                  std::string name) const
{
  return wrapped_solver->get_selector(s, con, name);
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

Term PrintingSolver::make_param(const std::string name, const Sort & sort) const
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

void PrintingSolver::get_unsat_assumptions(UnorderedTermSet & out) const
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
  // printed once the solver accepts it, so a refused one is not replayed
  wrapped_solver->set_logic(logic);
  (*out_stream) << "(" << SET_LOGIC_STR << " " << logic << ")" << std::endl;
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
  return std::make_shared<PrintingSolver>(std::move(wrapped_solver),
                                          out_stream);
}

SmtSolver create_printing_solver(SmtSolver wrapped_solver,
                                 std::ostream * out_stream,
                                 PrintingStyleEnum /* style */)
{
  return create_printing_solver(std::move(wrapped_solver), out_stream);
}

/* PrintingInterpolator */

PrintingInterpolator::PrintingInterpolator(SmtInterpolator s, std::ostream * os)
    : AbsSmtInterpolator(s->get_solver_enum(),
                         std::make_shared<PrintingSolver>(s, os)),
      wrapped_interpolator(std::move(s)),
      out_stream(os)
{
  if (get_solver_enum() == YICES2_INTERPOLATOR)
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
static std::string no_query_syntax(SolverEnum se)
{
  return "A printing interpolator cannot write the queries of " + to_string(se);
}

Result PrintingInterpolator::get_interpolant(const Term & A,
                                             const Term & B,
                                             Term & out_I) const
{
  switch (get_solver_enum())
  {
    case CVC5_INTERPOLATOR:
    case YICES2_INTERPOLATOR: {
      TermVec interpolant;
      Result r = print_query({ A, B }, interpolant);
      out_I = interpolant.front();
      return r;
    }
    // both define it as the sequence interpolant of A and B
    case BZLA_INTERPOLATOR:
    case MSAT_INTERPOLATOR: return interpolant_from_sequence(A, B, out_I);
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
  switch (get_solver_enum())
  {
    // Both split a sequence query into one get_interpolant query per split,
    // with sequence_from_interpolants, and keep what it reuses between
    // queries. Splitting it here the same way asks the same queries, and
    // prints each as it is asked.
    case CVC5_INTERPOLATOR:
    case YICES2_INTERPOLATOR:
      return sequence_from_interpolants(formulae, out_I);
    // both answer it natively
    case BZLA_INTERPOLATOR:
    case MSAT_INTERPOLATOR: return print_query(formulae, out_I);
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

Result PrintingInterpolator::print_query(const TermVec & formulae,
                                         TermVec & out_I) const
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
    case CVC5_INTERPOLATOR: {
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
    case YICES2_INTERPOLATOR: {
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
}

void PrintingInterpolator::initialize()
{
  if (get_solver_enum() == YICES2_INTERPOLATOR)
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
