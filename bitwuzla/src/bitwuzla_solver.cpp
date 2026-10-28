/*********************                                                        */
/*! \file bitwuzla_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Po-Chun Chien
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bitwuzla implementation of AbsSmtSolver
**
**
**/

#include "bitwuzla_solver.h"

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <fstream>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "bitwuzla/cpp/bitwuzla.h"
#include "bitwuzla_term.h"
#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "solver_enums.h"
#include "solver_utils.h"
#include "utils.h"

namespace smt {

const std::unordered_map<PrimOp, bitwuzla::Kind> op2bkind(
    { /* Core Theory */
      { And, bitwuzla::Kind::AND },
      { Or, bitwuzla::Kind::OR },
      { Xor, bitwuzla::Kind::XOR },
      { Not, bitwuzla::Kind::NOT },
      { Implies, bitwuzla::Kind::IMPLIES },
      { Ite, bitwuzla::Kind::ITE },
      { Equal, bitwuzla::Kind::EQUAL },
      { Distinct, bitwuzla::Kind::DISTINCT },
      /* Uninterpreted Functions */
      { Apply, bitwuzla::Kind::APPLY },
      /* Fixed Size BitVector Theory */
      { Concat, bitwuzla::Kind::BV_CONCAT },
      { Extract, bitwuzla::Kind::BV_EXTRACT },  // Indexed
      { BVNot, bitwuzla::Kind::BV_NOT },
      { BVNeg, bitwuzla::Kind::BV_NEG },
      { BVAnd, bitwuzla::Kind::BV_AND },
      { BVOr, bitwuzla::Kind::BV_OR },
      { BVXor, bitwuzla::Kind::BV_XOR },
      { BVNand, bitwuzla::Kind::BV_NAND },
      { BVNor, bitwuzla::Kind::BV_NOR },
      { BVXnor, bitwuzla::Kind::BV_XNOR },
      { BVAdd, bitwuzla::Kind::BV_ADD },
      { BVSub, bitwuzla::Kind::BV_SUB },
      { BVMul, bitwuzla::Kind::BV_MUL },
      { BVUdiv, bitwuzla::Kind::BV_UDIV },
      { BVSdiv, bitwuzla::Kind::BV_SDIV },
      { BVUrem, bitwuzla::Kind::BV_UREM },
      { BVSrem, bitwuzla::Kind::BV_SREM },
      { BVSmod, bitwuzla::Kind::BV_SMOD },
      { BVShl, bitwuzla::Kind::BV_SHL },
      { BVAshr, bitwuzla::Kind::BV_ASHR },
      { BVLshr, bitwuzla::Kind::BV_SHR },
      { BVComp, bitwuzla::Kind::BV_COMP },
      { BVUlt, bitwuzla::Kind::BV_ULT },
      { BVUle, bitwuzla::Kind::BV_ULE },
      { BVUgt, bitwuzla::Kind::BV_UGT },
      { BVUge, bitwuzla::Kind::BV_UGE },
      { BVSlt, bitwuzla::Kind::BV_SLT },
      { BVSle, bitwuzla::Kind::BV_SLE },
      { BVSgt, bitwuzla::Kind::BV_SGT },
      { BVSge, bitwuzla::Kind::BV_SGE },
      { Zero_Extend, bitwuzla::Kind::BV_ZERO_EXTEND },  // Indexed
      { Sign_Extend, bitwuzla::Kind::BV_SIGN_EXTEND },  // Indexed
      { Repeat, bitwuzla::Kind::BV_REPEAT },            // Indexed
      { Rotate_Left, bitwuzla::Kind::BV_ROLI },         // Indexed
      { Rotate_Right, bitwuzla::Kind::BV_RORI },        // Indexed
      /* Array Theory */
      { Select, bitwuzla::Kind::ARRAY_SELECT },
      { Store, bitwuzla::Kind::ARRAY_STORE },
      /* Quantifiers */
      { Forall, bitwuzla::Kind::FORALL },
      { Exists, bitwuzla::Kind::EXISTS } });

const std::unordered_set<std::uint64_t> bvbases({ 2, 10, 16 });

/** Apply kind to args with Bitwuzla, throwing an IncorrectUsageException
 *  where Bitwuzla rejects the application, e.g. for the number or the sorts
 *  of its arguments
 */
static Term make_bzla_term(const std::shared_ptr<bitwuzla::TermManager> & tm,
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
  Instance(const std::shared_ptr<bitwuzla::TermManager> & term_manager,
           const bitwuzla::Options & bzla_options)
      : tm(term_manager), bzla(*tm, bzla_options)
  {
  }

  // bzla uses tm, so tm is declared first and outlives it
  std::shared_ptr<bitwuzla::TermManager> tm;
  bitwuzla::Bitwuzla bzla;
};

BzlaSolver::BzlaSolver()
    : AbsSmtSolver(BZLA),
      options(),
      tm(std::make_shared<bitwuzla::TermManager>())
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
  return bsort->sort;
}

void BzlaSolver::set_opt(const std::string option, const std::string value)
{
  if (option == "incremental")
  {
    // Bitwuzla does not distinguish between incremental and non-incremental
    // solving.
    return;
  }
  if (is_initialized())
  {
    // the Bitwuzla instance took its options when it was created
    throw IncorrectUsageException("Must set options before using solver.");
  }
  if (option == "time-limit")
  {
    // Bitwuzla expects this in milliseconds, but smt-switch uses seconds.
    options.set(bitwuzla::Option::TIME_LIMIT_PER, std::stod(value) * 1000);
  }
  else if (!options.is_valid(option))
  {
    throw SmtException("Bitwuzla backend does not support option: " + option);
  }
  else
  {
    try
    {
      options.set(option, value);
    }
    catch (const bitwuzla::Exception & exception)
    {
      std::string detail = exception.what();
      // Remove "invalid call to 'bitwuzla::Options::set(...)'" from exception
      // message.
      detail.erase(0, detail.find(")"));
      detail.erase(0, detail.find(","));
      throw IncorrectUsageException("Bitwuzla backend got bad option " + option
                                    + detail);
    }
  }
}

void BzlaSolver::set_logic(const std::string /* logic */)
{
  // no need to set logic in bitwuzla
  return;
}

void BzlaSolver::assert_formula(const Term & t)
{
  get_bitwuzla()->assert_formula(bzla_term(t));
}

Result BzlaSolver::check_sat()
{
  bitwuzla::Result r;
  try
  {
    r = get_bitwuzla()->check_sat();
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
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
    assert(r == bitwuzla::Result::UNKNOWN);
    return Result(UNKNOWN);
  }
}

Result BzlaSolver::check_sat_assuming(const TermVec & assumptions)
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
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
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
    assert(res == bitwuzla::Result::UNKNOWN);
    return Result(UNKNOWN);
  }
}

void BzlaSolver::do_push(std::uint64_t num) { get_bitwuzla()->push(num); }

void BzlaSolver::do_pop(std::uint64_t num) { get_bitwuzla()->pop(num); }

Term BzlaSolver::get_value(const Term & t) const
{
  if (!instance)
  {
    throw IncorrectUsageException("Bitwuzla has no model before a check_sat");
  }
  return std::make_shared<BzlaTerm>(instance->bzla.get_value(bzla_term(t)), tm);
}

UnorderedTermMap BzlaSolver::get_array_values(const Term & arr,
                                              Term & out_const_base) const
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
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
  for (auto && elt : bcore)
  {
    out.insert(std::make_shared<BzlaTerm>(elt, tm));
  }
}

Sort BzlaSolver::make_sort(const std::string name, std::uint64_t arity) const
{
  if (arity != 0)
  {
    throw NotImplementedException(
        "Bitwuzla does not support parametrized uninterpreted sorts");
  }
  try
  {
    return std::make_shared<BzlaSort>(tm->mk_uninterpreted_sort(name), tm);
  }
  catch (bitwuzla::Exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort BzlaSolver::make_sort(SortKind sk) const
{
  if (sk == BOOL)
  {
    return std::make_shared<BzlaSort>(tm->mk_bool_sort(), tm);
  }
  else
  {
    throw NotImplementedException("Bitwuzla does not support sort "
                                  + to_string(sk));
  }
}

Sort BzlaSolver::make_sort(SortKind sk, uint64_t size) const
{
  if (sk == BV)
  {
    return std::make_shared<BzlaSort>(tm->mk_bv_sort(size), tm);
  }
  else
  {
    std::string msg("Can't create sort from sort kind ");
    msg += to_string(sk);
    msg += " with int argument.";
    throw IncorrectUsageException(msg);
  }
}

Sort BzlaSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  if (sk == FUNCTION)
  {
    if (sorts.size() < 2)
    {
      throw IncorrectUsageException(
          "Function sort must have >=2 sort arguments.");
    }

    bitwuzla::Sort bzla_return_sort = bzla_sort(sorts.back());

    // arity is one less, because last sort is return sort
    std::uint32_t arity = sorts.size() - 1;
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
    std::string msg("Can't create sort from sort kind ");
    msg += to_string(sk);
    msg += " with a vector of sorts of size " + std::to_string(sorts.size());
    throw IncorrectUsageException(msg);
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
{
  SortKind sk = sort->get_sort_kind();
  if (sk != BV)
  {
    throw NotImplementedException(
        "Bitwuzla does not support creating values for sort kind"
        + to_string(sk));
  }

  return std::make_shared<BzlaTerm>(tm->mk_bv_value_int64(bzla_sort(sort), i),
                                    tm);
}

Term BzlaSolver::make_term(const std::string val,
                           const Sort & sort,
                           std::uint64_t base) const
{
  SortKind sk = sort->get_sort_kind();
  if (sk != BV)
  {
    throw NotImplementedException(
        "Bitwuzla does not support creating values for sort kind"
        + to_string(sk));
  }

  if (bvbases.count(base) == 0)
  {
    throw IncorrectUsageException(::std::to_string(base) + " base for creating a BV value is not supported."
                                  " Options are 2, 10, and 16");
  }

  bitwuzla::Sort bsort = bzla_sort(sort);
  try
  {
    return std::make_shared<BzlaTerm>(tm->mk_bv_value(bsort, val, base), tm);
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
    throw NotImplementedException(
        "Bitwuzla has not make_sort(Term, Sort) for SortKind: "
        + to_string(sk));
  }
  else if (val->get_sort() != sort->get_elemsort())
  {
    throw IncorrectUsageException(
        "Value used to create constant array must match element sort.");
  }

  return std::make_shared<BzlaTerm>(tm->mk_const_array(bsort, bterm), tm);
}

Term BzlaSolver::make_symbol(const std::string name, const Sort & sort)
{
  if (symbol_table.find(name) != symbol_table.end())
  {
    throw IncorrectUsageException("Symbol name " + name + " already used.");
  }
  Term sym =
      std::make_shared<BzlaTerm>(tm->mk_const(bzla_sort(sort), name), tm);
  symbol_table[name] = sym;
  return sym;
}

Term BzlaSolver::get_symbol(const std::string & name) const
{
  auto it = symbol_table.find(name);
  if (it == symbol_table.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist.");
  }
  return it->second;
}

Term BzlaSolver::make_param(const std::string name, const Sort & sort) const
{
  return std::make_shared<BzlaTerm>(tm->mk_var(bzla_sort(sort), name), tm);
}

Term BzlaSolver::make_term(Op op, const TermVec & terms) const
{
  if (op.prim_op == Forall || op.prim_op == Exists)
  {
    check_quantifier_binders(op, terms);
  }

  std::vector<bitwuzla::Term> bitwuzla_terms;
  for (auto && t : terms)
  {
    bitwuzla_terms.push_back(bzla_term(t));
  }

  auto it = op2bkind.find(op.prim_op);
  if (it == op2bkind.end())
  {
    throw IncorrectUsageException("Bitwuzla does not yet support operator: "
                                  + op.to_string());
  }
  bitwuzla::Kind bkind = it->second;

  if (!op.num_idx)
  {
    return make_bzla_term(tm, bkind, bitwuzla_terms);
  }
  else
  {
    assert(op.num_idx > 0 && op.num_idx <= 2);
    std::vector<uint64_t> indices({ op.idx0 });
    if (op.num_idx == 2)
    {
      indices.push_back(op.idx1);
    }
    return make_bzla_term(tm, bkind, bitwuzla_terms, indices);
  }
}

void BzlaSolver::do_reset()
{
  // forget the symbols, so that their names can be declared again
  symbol_table.clear();
  instance.reset();
  options = {};
  tm = std::make_shared<bitwuzla::TermManager>();
  // get_bitwuzla() creates the instance on first use, so options can be
  // set again until then, as after construction
}

void BzlaSolver::do_reset_assertions()
{
  instance = std::make_shared<Instance>(tm, options);
}

Term BzlaSolver::substitute(const Term term,
                            const UnorderedTermMap & substitution_map) const
{
  bitwuzla::Term bterm = bzla_term(term);
  std::unordered_map<bitwuzla::Term, bitwuzla::Term> substitution_bterms_map;
  substitution_bterms_map.reserve(substitution_map.size());
  for (auto && elem : substitution_map)
  {
    if (!elem.first->is_symbolic_const() && !elem.first->is_param())
    {
      throw SmtException(
          "Bitwuzla backend doesn't support substitution with non symbol keys");
    }
    substitution_bterms_map.insert(
        { bzla_term(elem.first), bzla_term(elem.second) });
  }
  return std::make_shared<BzlaTerm>(
      tm->substitute_term(bterm, substitution_bterms_map), tm);
}

TermVec BzlaSolver::substitute_terms(
    const TermVec & terms, const UnorderedTermMap & substitution_map) const
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
      throw SmtException(
          "Bitwuzla backend doesn't support substitution with non symbol keys");
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

void BzlaSolver::dump_smt2(std::string filename) const
{
  std::ofstream out(filename);
  if (instance)
  {
    instance->bzla.print_formula(out, "smt2");
  }
  else
  {
    // a throwaway instance prints the same empty formula, without fixing
    // this solver's options
    bitwuzla::Bitwuzla(*tm, options).print_formula(out, "smt2");
  }
}

BzlaInterpolatingSolver::BzlaInterpolatingSolver()
    : AbsSmtInterpolator(BZLA_INTERPOLATOR, std::make_shared<BzlaSolver>()),
      bzla_solver(std::static_pointer_cast<BzlaSolver>(backend_solver))
{
  initialize();
}

void BzlaInterpolatingSolver::initialize()
{
  bzla_solver->set_opt("produce-interpolants", "true");
}

void BzlaInterpolatingSolver::do_set_opt(const std::string & option,
                                         const std::string & value)
{
  if (disallowed_options.find(option) != disallowed_options.end())
  {
    throw IncorrectUsageException(
        "Bitwuzla interpolator does not allow option: " + option);
  }
  if (option == "dump-queries")
  {
    // A special option for dumping interpolation queries to files.
    // The value is expected to contain a filename prefix.
    if (value.empty())
    {
      throw IncorrectUsageException(
          "Invalid value for option 'dump-queries', "
          "expected a non-empty string");
    }
    dump_queries_prefix = value;
    return;
  }
  bzla_solver->set_opt(option, value);
}

// delegate the interpolation procedure to `get_sequence_interpolants`
Result BzlaInterpolatingSolver::get_interpolant(const Term & A,
                                                const Term & B,
                                                Term & out_I) const
{
  return interpolant_from_sequence(A, B, out_I);
}

Result BzlaInterpolatingSolver::get_sequence_interpolants(
    const TermVec & formulae, TermVec & out_I) const
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
  // refuse a formula from another term manager before changing any state
  std::vector<bitwuzla::Term> bformulae;
  bformulae.reserve(formulae.size());
  for (const Term & f : formulae)
  {
    bformulae.push_back(bzla_solver->bzla_term(f));
  }
  // count how many assertions can be reused; none when incremental is off,
  // so every formula the last query pushed is popped below
  size_t num_reused = 0;
  while (incremental_mode && num_reused < last_itp_query_assertions.size()
         && num_reused < formulae.size()
         && last_itp_query_assertions.at(num_reused) == formulae.at(num_reused))
  {
    ++num_reused;
  }

  // pop formulas that cannot be reused
  bzla_solver->get_bitwuzla()->pop(last_itp_query_assertions.size()
                                   - num_reused);

  // update the interpolation groups and assertions
  last_itp_query_assertions.resize(num_reused);
  last_itp_query_assertions.reserve(formulae.size());

  // add new assertions from formulas
  for (size_t k = num_reused; k < formulae.size(); ++k)
  {
    // Add a new backtrack point and push the formula.
    bzla_solver->get_bitwuzla()->push(1);
    bzla_solver->get_bitwuzla()->assert_formula(bformulae.at(k));
    last_itp_query_assertions.push_back(formulae.at(k));
  }
  assert(formulae == last_itp_query_assertions);

  if (!dump_queries_prefix.empty())
  {
    // Note: the dumped query will only include the current assertions
    std::ofstream out(dump_queries_prefix + "."
                      + std::to_string(itp_query_count) + ".smt2");
    bzla_solver->get_bitwuzla()->print_formula(out, "smt2");
    out.close();
  }
  itp_query_count++;

  // solve query and get interpolants
  bitwuzla::Result bzla_res;
  try
  {
    bzla_res = bzla_solver->get_bitwuzla()->check_sat();
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }

  if (bzla_res == bitwuzla::Result::SAT)
  {
    return Result(SAT);
  }
  else if (bzla_res == bitwuzla::Result::UNKNOWN)
  {
    return Result(UNKNOWN, "Interpolation failure");
  }

  // if the result is not UNSAT, we cannot interpolate
  assert(bzla_res == bitwuzla::Result::UNSAT);

  Result r = Result(UNSAT);
  std::vector<std::vector<bitwuzla::Term>> partitions;
  for (size_t i = 0, n = formulae.size() - 1; i < n; ++i)
  {
    partitions.push_back({ bformulae.at(i) });
  }
  const std::vector<bitwuzla::Term> itps =
      bzla_solver->get_bitwuzla()->get_interpolants(partitions);
  // the interpolants belong to the term manager of the formulae
  const std::shared_ptr<bitwuzla::TermManager> & formulae_tm =
      backend_pointer_cast<BzlaTerm>(formulae.at(0))->tm;
  for (const auto & itp : itps)
  {
    if (itp.is_null())
    {
      Term nullterm;
      out_I.push_back(nullterm);
      r = Result(UNKNOWN,
                 "Had at least one interpolation failure in "
                 "get_sequence_interpolants.");
    }
    else
    {
      out_I.push_back(std::make_shared<BzlaTerm>(itp, formulae_tm));
    }
  }

  assert(out_I.size() == formulae.size() - 1);
  return r;
}

// these terms belong to the term manager a reset destroys
void BzlaInterpolatingSolver::forget_queries()
{
  last_itp_query_assertions.clear();
}

}  // namespace smt
