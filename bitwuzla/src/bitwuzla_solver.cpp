/*!
 * \file bitwuzla_solver.cpp
 * \brief Bitwuzla implementation of AbsSmtSolver
 * \author Makai Mann
 * \author Samantha Archer
 * \author Po-Chun Chien
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/bitwuzla_solver.h"

#include <bitwuzla/cpp/bitwuzla.h>

#include <cstddef>
#include <cstdint>
#include <exception>
#include <fstream>
#include <initializer_list>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "smt-switch/bitwuzla_sort.h"
#include "smt-switch/bitwuzla_term.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_utils.h"
#include "smt-switch/utils.h"

namespace smt {

/** Apply kind to args with Bitwuzla, throwing an IncorrectUsageException
 *  where Bitwuzla rejects the application, e.g. for the number or the sorts
 *  of its arguments
 */
static Term make_bzla_term(const std::shared_ptr<BzlaTermManager> & tm,
                           bitwuzla::Kind kind,
                           const std::vector<bitwuzla::Term> & args,
                           const std::vector<std::uint64_t> & indices = {})
{
  try
  {
    return std::make_shared<BzlaTerm>(tm->mk_term(kind, args, indices), tm);
  }
  catch (const bitwuzla::Exception & e)
  {
    throw IncorrectUsageException(e.what());
  }
}

struct BzlaSolver::Instance
{
  Instance(const std::shared_ptr<BzlaTermManager> & term_manager,
           const bitwuzla::Options & bzla_options)
      : tm(term_manager), bzla(*tm, bzla_options)
  {
  }

  // bzla uses tm, so tm is declared first and outlives it
  std::shared_ptr<BzlaTermManager> tm;
  bitwuzla::Bitwuzla bzla;
};

BzlaSolver::BzlaSolver()
    : AbsSmtSolver(BZLA), tm(std::make_shared<BzlaTermManager>())
{
}

std::shared_ptr<bitwuzla::Bitwuzla> BzlaSolver::get_bitwuzla()
{
  if (!instance)
  {
    instance = std::make_shared<Instance>(tm, options);
  }
  return std::shared_ptr<bitwuzla::Bitwuzla>(instance, &instance->bzla);
}

std::shared_ptr<bitwuzla::TermManager> BzlaSolver::get_term_manager()
{
  return tm;
}

bool BzlaSolver::is_initialized() const { return instance != nullptr; }

bitwuzla::Term BzlaSolver::bzla_term(const Term & t) const
{
  std::shared_ptr<BzlaTerm> bterm = backend_pointer_cast<BzlaTerm>(t);
  if (bterm->tm != tm)
  {
    throw IncorrectUsageException("Term " + t->to_string()
                                  + " was made by another solver");
  }
  return bterm->term;
}

bitwuzla::Sort BzlaSolver::bzla_sort(const Sort & s) const
{
  std::shared_ptr<BzlaSort> bsort = backend_pointer_cast<BzlaSort>(s);
  if (bsort->tm != tm)
  {
    throw IncorrectUsageException("Sort " + s->to_string()
                                  + " was made by another solver");
  }
  return bsort->get_bitwuzla_sort();
}

void BzlaSolver::set_opt(const std::string option, const std::string value)
{
  if (option == "incremental")
  {
    if (!bool_option_value(option, value))
    {
      throw NotImplementedException("Bitwuzla cannot turn off " + option);
    }
    return;
  }
  if (is_initialized())
  {
    // the Bitwuzla instance took its options when it was created
    throw IncorrectUsageException(
        "Options must be set before the solver is used");
  }
  if (option == "time-limit")
  {
    // Bitwuzla expects this in milliseconds, but smt-switch uses seconds.
    options.set(bitwuzla::Option::TIME_LIMIT_PER,
                time_limit_milliseconds(value));
  }
  else if (!options.is_valid(option))
  {
    throw NotImplementedException("Bitwuzla does not support the option "
                                  + option);
  }
  else
  {
    // Bitwuzla also takes 1 and 0 for these, which SMT-LIB does not.
    std::string bzla_value = value;
    if (option == "produce-models" || option == "produce-unsat-assumptions")
    {
      bzla_value = bool_option_value(option, value) ? "true" : "false";
    }
    try
    {
      // Bitwuzla checks a number against the option's range only when given
      // it as a number. Up to 19 digits always fit in 64 bits.
      bitwuzla::Option opt = options.option(option.c_str());
      if (options.is_numeric(opt) && is_decimal_numeral(value)
          && value.size() <= 19)
      {
        options.set(opt, std::stoull(value));
      }
      else
      {
        options.set(option, bzla_value);
      }
    }
    catch (const bitwuzla::Exception & exception)
    {
      std::string detail = exception.what();
      // Bitwuzla's argument checks start with "invalid call to '<the
      // function>', ", which says nothing to the caller.
      const std::string call_prefix = "invalid call to '";
      std::string::size_type call_end = detail.find("', ");
      if (detail.compare(0, call_prefix.size(), call_prefix) == 0
          && call_end != std::string::npos)
      {
        detail.erase(0, call_end + 3);
      }
      throw IncorrectUsageException("Bitwuzla got a bad value for the option "
                                    + option + ": " + detail);
    }
  }
}

void BzlaSolver::set_logic(const std::string logic)
{
  if (!is_smtlib_logic(logic))
  {
    throw IncorrectUsageException(logic + " is not an SMT-LIB logic");
  }
  // AX is refused by the bitwuzla binary, but this backend handles it
  // through uninterpreted sorts
  if (logic == "ALL" || logic == "AX" || logic == "QF_AX")
  {
    logic_ = logic;
    return;
  }
  // an optional QF_ followed by at least one of A, UF, BV and FPLRA or FP,
  // in that order, as the bitwuzla binary accepts
  std::string_view theories = logic;
  if (theories.substr(0, 3) == "QF_")
  {
    theories.remove_prefix(3);
  }
  std::string_view rest = theories;
  for (std::string_view theory : { "A", "UF", "BV" })
  {
    if (rest.substr(0, theory.size()) == theory)
    {
      rest.remove_prefix(theory.size());
    }
  }
  if (theories.empty() || !(rest.empty() || rest == "FP" || rest == "FPLRA"))
  {
    throw NotImplementedException("Bitwuzla does not support the logic "
                                  + logic);
  }
  logic_ = logic;
}

void BzlaSolver::do_assert(const Term & t)
try
{
  get_bitwuzla()->assert_formula(bzla_term(t));
}
catch (const bitwuzla::Exception & e)
{
  throw IncorrectUsageException(e.what());
}

Result BzlaSolver::check_sat()
{
  bitwuzla::Result r;
  try
  {
    r = get_bitwuzla()->check_sat();
  }
  // Bitwuzla raises its own exception for a call its API does not allow
  catch (const bitwuzla::Exception & e)
  {
    throw IncorrectUsageException(e.what());
  }
  catch (std::exception & e)
  {
    throw SolverException(e.what());
  }

  if (r == bitwuzla::Result::SAT)
  {
    return Result(SAT);
  }
  else if (r == bitwuzla::Result::UNSAT)
  {
    return Result(UNSAT);
  }
  else
  {
    return Result(UNKNOWN);
  }
}

Result BzlaSolver::do_check_sat_assuming(const TermVec & assumptions)
{
  std::vector<bitwuzla::Term> bzla_assumptions;
  bzla_assumptions.reserve(assumptions.size());
  for (const Term & a : assumptions)
  {
    bzla_assumptions.push_back(bzla_term(a));
  }

  bitwuzla::Result res;
  try
  {
    res = get_bitwuzla()->check_sat(bzla_assumptions);
  }
  catch (const bitwuzla::Exception & e)
  {
    throw IncorrectUsageException(e.what());
  }
  catch (std::exception & e)
  {
    throw SolverException(e.what());
  }

  if (res == bitwuzla::Result::SAT)
  {
    return Result(SAT);
  }
  else if (res == bitwuzla::Result::UNSAT)
  {
    return Result(UNSAT);
  }
  else
  {
    return Result(UNKNOWN);
  }
}

void BzlaSolver::do_push(std::uint64_t num)
try
{
  get_bitwuzla()->push(narrow_levels(num));
}
catch (const bitwuzla::Exception & e)
{
  throw IncorrectUsageException(e.what());
}

void BzlaSolver::do_pop(std::uint64_t num)
try
{
  get_bitwuzla()->pop(narrow_levels(num));
}
catch (const bitwuzla::Exception & e)
{
  throw IncorrectUsageException(e.what());
}

Term BzlaSolver::get_value(const Term & t) const
try
{
  if (!instance)
  {
    throw IncorrectUsageException("Bitwuzla has no model before a check_sat");
  }
  return std::make_shared<BzlaTerm>(instance->bzla.get_value(bzla_term(t)), tm);
}
catch (const bitwuzla::Exception & e)
{
  throw IncorrectUsageException(e.what());
}

UnorderedTermMap BzlaSolver::get_array_values(const Term & arr,
                                              Term & out_const_base) const
try
{
  out_const_base = nullptr;
  if (!instance)
  {
    throw IncorrectUsageException("Bitwuzla has no model before a check_sat");
  }
  // Bitwuzla gives an array model as a chain of stores over a constant
  // base, outermost store first.
  bitwuzla::Term bval = instance->bzla.get_value(bzla_term(arr));

  std::vector<std::pair<Term, Term>> stores;
  while (bval.kind() == bitwuzla::Kind::ARRAY_STORE)
  {
    std::vector<bitwuzla::Term> children = bval.children();
    stores.push_back({ std::make_shared<BzlaTerm>(children[1], tm),
                       std::make_shared<BzlaTerm>(children[2], tm) });
    bval = children[0];
  }

  if (bval.kind() != bitwuzla::Kind::CONST_ARRAY)
  {
    // Nothing else is expected under the stores. Say which head turned up
    // rather than return a map that quietly omits it.
    throw NotImplementedException("Bitwuzla gave an array model headed by "
                                  + bval.str()
                                  + ", which has no constant base");
  }
  out_const_base = std::make_shared<BzlaTerm>(bval.children()[0], tm);

  return store_chain_values(stores);
}
catch (const bitwuzla::Exception & e)
{
  throw IncorrectUsageException(e.what());
}

void BzlaSolver::get_unsat_assumptions(UnorderedTermSet & out) const
{
  if (!instance)
  {
    throw IncorrectUsageException(
        "Bitwuzla has no unsat assumptions before a check_sat_assuming");
  }
  std::vector<bitwuzla::Term> bcore;
  try
  {
    bcore = instance->bzla.get_unsat_assumptions();
  }
  catch (const bitwuzla::Exception & e)
  {
    throw IncorrectUsageException(e.what());
  }
  catch (std::exception & e)
  {
    throw SolverException(e.what());
  }
  for (auto && elt : bcore)
  {
    out.insert(std::make_shared<BzlaTerm>(elt, tm));
  }
}

Sort BzlaSolver::make_sort(const std::string name, std::uint64_t arity) const
{
  if (is_internal_name(name))
  {
    throw IncorrectUsageException("Sort name " + name + " starts with "
                                  + std::string(INTERNAL_NAME_PREFIX)
                                  + ", which is reserved for internal use");
  }
  if (arity)
  {
    return std::make_shared<BzlaSort>(tm->add_constructor(name, arity), tm);
  }
  try
  {
    return std::make_shared<BzlaSort>(tm->mk_uninterpreted_sort(name), tm);
  }
  catch (bitwuzla::Exception & e)
  {
    throw IncorrectUsageException(e.what());
  }
}

Sort BzlaSolver::make_sort(const Sort & sort_con, const SortVec & sorts) const
{
  std::shared_ptr<BzlaSort> bcon = backend_pointer_cast<BzlaSort>(sort_con);
  if (bcon->tm != tm)
  {
    throw IncorrectUsageException("Sort " + sort_con->to_string()
                                  + " was made by another solver");
  }
  if (bcon->get_sort_kind() != UNINTERPRETED_CONS)
  {
    throw IncorrectUsageException("Sort " + sort_con->to_string()
                                  + " is not a sort constructor");
  }
  std::size_t arity = bcon->get_arity();
  if (sorts.size() != arity)
  {
    throw IncorrectUsageException(
        "Expected " + std::to_string(arity) + " sort arguments to "
        + sort_con->to_string() + " but got " + std::to_string(sorts.size()));
  }
  // Bitwuzla prints a sort's symbol as is, so it is the applied sort's
  // SMT-LIB text
  std::string symbol =
      "(" + smtlib_quote_symbol(bcon->get_uninterpreted_name());
  std::vector<bitwuzla::Sort> params;
  params.reserve(sorts.size());
  for (const Sort & s : sorts)
  {
    params.push_back(bzla_sort(s));
    symbol += " " + s->to_string();
  }
  symbol += ")";
  return std::make_shared<BzlaSort>(
      tm->add_instance(bcon->constructor_id, params, symbol), tm);
}

Sort BzlaSolver::make_sort(SortKind sk) const
{
  if (sk == BOOL)
  {
    return std::make_shared<BzlaSort>(tm->mk_bool_sort(), tm);
  }
  else if (sk == INT || sk == REAL || sk == STRING)
  {
    throw NotImplementedException("Bitwuzla does not support sort "
                                  + to_string(sk));
  }
  else
  {
    throw IncorrectUsageException("Can't make a sort of kind " + to_string(sk)
                                  + " without arguments");
  }
}

Sort BzlaSolver::make_sort(SortKind sk, uint64_t size) const
try
{
  if (sk == BV)
  {
    return std::make_shared<BzlaSort>(tm->mk_bv_sort(size), tm);
  }
  else
  {
    throw IncorrectUsageException("Can't make a sort of kind " + to_string(sk)
                                  + " from an integer");
  }
}
catch (const bitwuzla::Exception & e)
{
  throw IncorrectUsageException(e.what());
}

Sort BzlaSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  if (sk == FUNCTION)
  {
    if (sorts.size() < 2)
    {
      throw IncorrectUsageException("A function sort needs at least two sorts");
    }

    bitwuzla::Sort bzla_return_sort = bzla_sort(sorts.back());

    // arity is one less, because last sort is return sort
    std::size_t arity = sorts.size() - 1;
    std::vector<bitwuzla::Sort> bzla_sorts;
    bzla_sorts.reserve(arity);
    for (std::size_t i = 0; i < arity; i++)
    {
      bzla_sorts.push_back(bzla_sort(sorts[i]));
    }

    return std::make_shared<BzlaSort>(
        tm->mk_fun_sort(bzla_sorts, { bzla_return_sort }), tm);
  }
  else if (sk == ARRAY && sorts.size() == 2)
  {
    return std::make_shared<BzlaSort>(
        tm->mk_array_sort(bzla_sort(sorts[0]), bzla_sort(sorts[1])), tm);
  }
  else
  {
    throw IncorrectUsageException("Can't make a sort of kind " + to_string(sk)
                                  + " from " + std::to_string(sorts.size())
                                  + " sorts");
  }
}

Term BzlaSolver::make_term(bool b) const
{
  if (b)
  {
    return std::make_shared<BzlaTerm>(tm->mk_true(), tm);
  }
  else
  {
    return std::make_shared<BzlaTerm>(tm->mk_false(), tm);
  }
}

Term BzlaSolver::make_term(std::int64_t i, const Sort & sort) const
try
{
  SortKind sk = sort->get_sort_kind();
  if (sk == INT || sk == REAL)
  {
    throw NotImplementedException(
        "Bitwuzla does not support values of sort kind " + to_string(sk));
  }
  if (sk != BV)
  {
    throw IncorrectUsageException("Can't create value " + std::to_string(i)
                                  + " with sort " + sort->to_string());
  }

  return std::make_shared<BzlaTerm>(tm->mk_bv_value_int64(bzla_sort(sort), i),
                                    tm);
}
catch (const bitwuzla::Exception & e)
{
  throw IncorrectUsageException(e.what());
}

Term BzlaSolver::make_term(const std::string val,
                           const Sort & sort,
                           std::uint64_t base) const
{
  SortKind sk = sort->get_sort_kind();
  if (sk == INT || sk == REAL)
  {
    throw NotImplementedException(
        "Bitwuzla does not support values of sort kind " + to_string(sk));
  }
  if (sk != BV)
  {
    throw IncorrectUsageException("Can't create value " + val + " with sort "
                                  + sort->to_string());
  }

  bitwuzla::Sort bsort = bzla_sort(sort);
  std::uint64_t width = sort->get_width();
  try
  {
    return std::make_shared<BzlaTerm>(
        width <= 64
            ? tm->mk_bv_value_uint64(
                  bsort, detail::bv_value_to_uint64(val, base, width))
            : tm->mk_bv_value(bsort, bv_value_to_bits(val, base, sort), 2),
        tm);
  }
  catch (bitwuzla::Exception & e)
  {
    throw IncorrectUsageException(e.what());
  }
}

Term BzlaSolver::make_term(const Term & val, const Sort & sort) const
{
  bitwuzla::Sort bsort = bzla_sort(sort);
  bitwuzla::Term bterm = bzla_term(val);
  SortKind sk = sort->get_sort_kind();
  if (sk != ARRAY)
  {
    throw IncorrectUsageException("Can't make a constant array of sort "
                                  + sort->to_string()
                                  + ", which is not an array sort");
  }
  else if (val->get_sort() != sort->get_elemsort())
  {
    throw IncorrectUsageException(
        "The value of a constant array must have the array's element sort");
  }

  return std::make_shared<BzlaTerm>(tm->mk_const_array(bsort, bterm), tm);
}

Term BzlaSolver::make_symbol(const std::string name, const Sort & sort)
try
{
  if (symbol_table.find(name) != symbol_table.end())
  {
    throw IncorrectUsageException("Symbol " + name + " has already been used");
  }
  Term sym =
      std::make_shared<BzlaTerm>(tm->mk_const(bzla_sort(sort), name), tm);
  symbol_table[name] = sym;
  return sym;
}
catch (const bitwuzla::Exception & e)
{
  throw IncorrectUsageException(e.what());
}

Term BzlaSolver::get_symbol(const std::string & name) const
{
  auto it = symbol_table.find(name);
  if (it == symbol_table.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist");
  }
  return it->second;
}

Term BzlaSolver::make_param(const std::string name, const Sort & sort) const
try
{
  return std::make_shared<BzlaTerm>(tm->mk_var(bzla_sort(sort), name), tm);
}
catch (const bitwuzla::Exception & e)
{
  throw IncorrectUsageException(e.what());
}

Term BzlaSolver::make_term(Op op, const TermVec & terms) const
{
  if (op.prim_op == Forall || op.prim_op == Exists)
  {
    check_quantifier_binders(op, terms);
  }
  // Bitwuzla 0.9.1 and older make a term of width 0 instead of refusing.
  if (op.prim_op == Repeat && op.indices[0] == 0)
  {
    throw IncorrectUsageException("Repeat needs a count of at least 1");
  }

  std::vector<bitwuzla::Term> bitwuzla_terms;
  for (auto && t : terms)
  {
    bitwuzla_terms.push_back(bzla_term(t));
  }

  const bitwuzla::Kind bkind = to_bitwuzla_kind(op.prim_op);

  return make_bzla_term(
      tm,
      bkind,
      bitwuzla_terms,
      std::vector<std::uint64_t>(op.indices.begin(), op.indices.end()));
}

void BzlaSolver::do_reset()
{
  // forget the symbols, so that their names can be declared again
  symbol_table.clear();
  instance.reset();
  options = {};
  logic_ = "ALL";
  tm = std::make_shared<BzlaTermManager>();
  // get_bitwuzla() creates the instance on first use, so options can be
  // set again until then, as after construction
}

void BzlaSolver::do_reset_assertions()
{
  instance = std::make_shared<Instance>(tm, options);
}

Term BzlaSolver::substitute(const Term term,
                            const UnorderedTermMap & substitution_map) const
try
{
  bitwuzla::Term bterm = bzla_term(term);
  std::unordered_map<bitwuzla::Term, bitwuzla::Term> substitution_bterms_map;
  substitution_bterms_map.reserve(substitution_map.size());
  for (auto && elem : substitution_map)
  {
    if (!elem.first->is_symbolic_const() && !elem.first->is_param())
    {
      throw Exception(
          "Bitwuzla does not support substituting a term that is neither a "
          "symbol nor a param");
    }
    substitution_bterms_map.insert(
        { bzla_term(elem.first), bzla_term(elem.second) });
  }
  return std::make_shared<BzlaTerm>(
      tm->substitute_term(bterm, substitution_bterms_map), tm);
}
catch (const bitwuzla::Exception & e)
{
  throw IncorrectUsageException(e.what());
}

TermVec BzlaSolver::substitute_terms(
    const TermVec & terms, const UnorderedTermMap & substitution_map) const
try
{
  std::vector<bitwuzla::Term> bterms;
  std::size_t terms_size = terms.size();
  bterms.reserve(terms_size);
  for (auto && t : terms)
  {
    bterms.push_back(bzla_term(t));
  }
  std::unordered_map<bitwuzla::Term, bitwuzla::Term> substitution_bterms_map;
  substitution_bterms_map.reserve(substitution_map.size());
  for (auto && elem : substitution_map)
  {
    if (!elem.first->is_symbolic_const() && !elem.first->is_param())
    {
      throw Exception(
          "Bitwuzla does not support substituting a term that is neither a "
          "symbol nor a param");
    }
    substitution_bterms_map.insert(
        { bzla_term(elem.first), bzla_term(elem.second) });
  }
  tm->substitute_terms(bterms, substitution_bterms_map);

  TermVec res;
  res.reserve(terms_size);
  for (auto && t : bterms)
  {
    res.push_back(std::make_shared<BzlaTerm>(t, tm));
  }
  return res;
}
catch (const bitwuzla::Exception & e)
{
  throw IncorrectUsageException(e.what());
}

void BzlaSolver::dump_smt2(std::string filename) const
{
  // Bitwuzla's print_formula declares no uninterpreted sort
  TermVec assertions;
  if (instance)
  {
    for (const bitwuzla::Term & a : instance->bzla.get_assertions())
    {
      assertions.push_back(std::make_shared<BzlaTerm>(a, tm));
    }
  }
  std::ofstream out(filename);
  if (!out)
  {
    throw SystemException("Cannot open " + filename + " for writing");
  }
  smtlib_benchmark(out, logic_, assertions);
  out.close();
  if (!out)
  {
    throw SystemException("Cannot write " + filename);
  }
}

}  // namespace smt
