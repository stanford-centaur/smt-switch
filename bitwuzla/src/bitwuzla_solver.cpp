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
#include "result.h"
#include "smt.h"
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

BzlaSolver::BzlaSolver()
    : AbsSmtSolver(BZLA),
      options(),
      tm(std::make_unique<bitwuzla::TermManager>()),
      context_level(0)
{
}

BzlaSolver::~BzlaSolver()
{
  // the terms in symbol_table belong to tm, so release them before it
  symbol_table.clear();
}

bitwuzla::Bitwuzla * BzlaSolver::get_bitwuzla() const
{
  if (!bzla)
  {
    bzla = std::make_unique<bitwuzla::Bitwuzla>(*tm, options);
  }
  return bzla.get();
}

bool BzlaSolver::is_initialized() const { return bzla != nullptr; }

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
  std::shared_ptr<BzlaTerm> bterm = std::static_pointer_cast<BzlaTerm>(t);
  get_bitwuzla()->assert_formula(bterm->term);
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
  return check_sat_assuming_internal(assumptions);
}

void BzlaSolver::push(std::uint64_t num)
{
  get_bitwuzla()->push(num);
  context_level += num;
}

void BzlaSolver::pop(std::uint64_t num)
{
  get_bitwuzla()->pop(num);
  context_level -= num;
}

uint64_t BzlaSolver::get_context_level() const { return context_level; }

Term BzlaSolver::get_value(const Term & t) const
{
  std::shared_ptr<BzlaTerm> bterm = std::static_pointer_cast<BzlaTerm>(t);
  return std::make_shared<BzlaTerm>(get_bitwuzla()->get_value(bterm->term));
}

UnorderedTermMap BzlaSolver::get_array_values(const Term & arr,
                                              Term & out_const_base) const
{
  throw NotImplementedException(
      "Bitwuzla backend doesn't support get_array_values yet");
}

void BzlaSolver::get_unsat_assumptions(UnorderedTermSet & out)
{
  std::vector<bitwuzla::Term> bcore;
  try
  {
    bcore = get_bitwuzla()->get_unsat_assumptions();
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
  for (auto && elt : bcore)
  {
    out.insert(std::make_shared<BzlaTerm>(elt));
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
    return std::make_shared<BzlaSort>(tm->mk_uninterpreted_sort(name));
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
    return std::make_shared<BzlaSort>(tm->mk_bool_sort());
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
    return std::make_shared<BzlaSort>(tm->mk_bv_sort(size));
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

    Sort returnsort = sorts.back();
    std::shared_ptr<BzlaSort> bzla_return_sort =
        std::static_pointer_cast<BzlaSort>(returnsort);

    // arity is one less, because last sort is return sort
    std::uint32_t arity = sorts.size() - 1;
    std::vector<bitwuzla::Sort> bzla_sorts;
    bzla_sorts.reserve(arity);
    for (std::size_t i = 0; i < arity; i++)
    {
      std::shared_ptr<BzlaSort> bs =
          std::static_pointer_cast<BzlaSort>(sorts[i]);
      bzla_sorts.push_back(bs->sort);
    }

    return std::make_shared<BzlaSort>(
        tm->mk_fun_sort(bzla_sorts, { bzla_return_sort->sort }));
  }
  else if (sk == ARRAY && sorts.size() == 2)
  {
    std::shared_ptr<BzlaSort> bidxsort =
        std::static_pointer_cast<BzlaSort>(sorts[0]);
    std::shared_ptr<BzlaSort> belemsort =
        std::static_pointer_cast<BzlaSort>(sorts[1]);
    return std::make_shared<BzlaSort>(
        tm->mk_array_sort(bidxsort->sort, belemsort->sort));
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
    return std::make_shared<BzlaTerm>(tm->mk_true());
  }
  else
  {
    return std::make_shared<BzlaTerm>(tm->mk_false());
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

  std::shared_ptr<BzlaSort> bsort = std::static_pointer_cast<BzlaSort>(sort);
  return std::make_shared<BzlaTerm>(tm->mk_bv_value_int64(bsort->sort, i));
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

  std::shared_ptr<BzlaSort> bsort = std::static_pointer_cast<BzlaSort>(sort);
  try
  {
    return std::make_shared<BzlaTerm>(tm->mk_bv_value(bsort->sort, val, base));
  }
  catch (bitwuzla::Exception & e)
  {
    throw IncorrectUsageException(e.what());
  }
}

Term BzlaSolver::make_term(const Term & val, const Sort & sort) const
{
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

  std::shared_ptr<BzlaTerm> bterm = std::static_pointer_cast<BzlaTerm>(val);
  std::shared_ptr<BzlaSort> bsort = std::static_pointer_cast<BzlaSort>(sort);
  return std::make_shared<BzlaTerm>(
      tm->mk_const_array(bsort->sort, bterm->term));
}

Term BzlaSolver::make_symbol(const std::string name, const Sort & sort)
{
  if (symbol_table.find(name) != symbol_table.end())
  {
    throw IncorrectUsageException("Symbol name " + name + " already used.");
  }
  std::shared_ptr<BzlaSort> bsort = std::static_pointer_cast<BzlaSort>(sort);
  Term sym = std::make_shared<BzlaTerm>(tm->mk_const(bsort->sort, name));
  symbol_table[name] = sym;
  return sym;
}

Term BzlaSolver::get_symbol(const std::string & name)
{
  auto it = symbol_table.find(name);
  if (it == symbol_table.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist.");
  }
  return it->second;
}

Term BzlaSolver::make_param(const std::string name, const Sort & sort)
{
  std::shared_ptr<BzlaSort> bsort = std::static_pointer_cast<BzlaSort>(sort);
  return std::make_shared<BzlaTerm>(tm->mk_var(bsort->sort, name));
}

Term BzlaSolver::make_term(Op op, const Term & t) const
{
  std::shared_ptr<BzlaTerm> bterm = std::static_pointer_cast<BzlaTerm>(t);

  auto it = op2bkind.find(op.prim_op);
  if (it == op2bkind.end())
  {
    throw IncorrectUsageException("Bitwuzla does not yet support operator: "
                                  + op.to_string());
  }
  bitwuzla::Kind bkind = it->second;

  if (!op.num_idx)
  {
    return std::make_shared<BzlaTerm>(tm->mk_term(bkind, { bterm->term }));
  }
  else if (op.num_idx == 1)
  {
    return std::make_shared<BzlaTerm>(
        tm->mk_term(bkind, { bterm->term }, { op.idx0 }));
  }
  else
  {
    assert(op.num_idx == 2);
    return std::make_shared<BzlaTerm>(
        tm->mk_term(bkind, { bterm->term }, { op.idx0, op.idx1 }));
  }
}

Term BzlaSolver::make_term(Op op, const Term & t0, const Term & t1) const
{
  std::shared_ptr<BzlaTerm> bterm0 = std::static_pointer_cast<BzlaTerm>(t0);
  std::shared_ptr<BzlaTerm> bterm1 = std::static_pointer_cast<BzlaTerm>(t1);

  auto it = op2bkind.find(op.prim_op);
  if (it == op2bkind.end())
  {
    throw IncorrectUsageException("Bitwuzla does not yet support operator: "
                                  + op.to_string());
  }
  bitwuzla::Kind bkind = it->second;

  if (!op.num_idx)
  {
    return std::make_shared<BzlaTerm>(
        tm->mk_term(bkind, { bterm0->term, bterm1->term }));
  }
  else if (op.num_idx == 1)
  {
    return std::make_shared<BzlaTerm>(
        tm->mk_term(bkind, { bterm0->term, bterm1->term }, { op.idx0 }));
  }
  else
  {
    assert(op.num_idx == 2);
    return std::make_shared<BzlaTerm>(tm->mk_term(
        bkind, { bterm0->term, bterm1->term }, { op.idx0, op.idx1 }));
  }
}

Term BzlaSolver::make_term(Op op,
                           const Term & t0,
                           const Term & t1,
                           const Term & t2) const
{
  if (is_variadic(op.prim_op))
  {
    // rely on vector application for variadic applications
    // binary operators applied to multiple terms with "reduce" semantics
    return make_term(op, { t0, t1, t2 });
  }

  std::shared_ptr<BzlaTerm> bterm0 = std::static_pointer_cast<BzlaTerm>(t0);
  std::shared_ptr<BzlaTerm> bterm1 = std::static_pointer_cast<BzlaTerm>(t1);
  std::shared_ptr<BzlaTerm> bterm2 = std::static_pointer_cast<BzlaTerm>(t2);

  auto it = op2bkind.find(op.prim_op);
  if (it == op2bkind.end())
  {
    throw IncorrectUsageException("Bitwuzla does not yet support operator: "
                                  + op.to_string());
  }
  bitwuzla::Kind bkind = it->second;

  if (!op.num_idx)
  {
    return std::make_shared<BzlaTerm>(
        tm->mk_term(bkind, { bterm0->term, bterm1->term, bterm2->term }));
  }
  else
  {
    assert(op.num_idx > 0 && op.num_idx <= 1);
    const std::vector<bitwuzla::Term> bitwuzla_terms(
        { bterm0->term, bterm1->term, bterm2->term });
    std::vector<uint64_t> indices({ op.idx0 });
    if (op.num_idx == 2)
    {
      indices.push_back(op.idx1);
    }

    return std::make_shared<BzlaTerm>(
        tm->mk_term(bkind, bitwuzla_terms, indices));
  }
}

Term BzlaSolver::make_term(Op op, const TermVec & terms) const
{
  std::vector<bitwuzla::Term> bitwuzla_terms;
  for (auto && t : terms)
  {
    bitwuzla_terms.push_back(std::static_pointer_cast<BzlaTerm>(t)->term);
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
    return std::make_shared<BzlaTerm>(tm->mk_term(bkind, bitwuzla_terms));
  }
  else
  {
    assert(op.num_idx > 0 && op.num_idx <= 2);
    std::vector<uint64_t> indices({ op.idx0 });
    if (op.num_idx == 2)
    {
      indices.push_back(op.idx1);
    }
    return std::make_shared<BzlaTerm>(
        tm->mk_term(bkind, bitwuzla_terms, indices));
  }
}

void BzlaSolver::reset()
{
  // the terms in symbol_table belong to tm, so release them before it
  symbol_table.clear();
  bzla.reset();
  options = {};
  tm = std::make_unique<bitwuzla::TermManager>();
  // get_bitwuzla() creates the instance on first use, so options can be
  // set again until then, as after construction
  context_level = 0;
}

void BzlaSolver::reset_assertions()
{
  bzla.reset();
  bzla = std::make_unique<bitwuzla::Bitwuzla>(*tm, options);
  context_level = 0;
}

Term BzlaSolver::substitute(const Term term,
                            const UnorderedTermMap & substitution_map) const
{
  std::shared_ptr<BzlaTerm> bterm = std::static_pointer_cast<BzlaTerm>(term);
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
        { std::static_pointer_cast<BzlaTerm>(elem.first)->term,
          std::static_pointer_cast<BzlaTerm>(elem.second)->term });
  }
  return std::make_shared<BzlaTerm>(
      tm->substitute_term(bterm->term, substitution_bterms_map));
}

TermVec BzlaSolver::substitute_terms(
    const TermVec & terms, const UnorderedTermMap & substitution_map) const
{
  std::vector<bitwuzla::Term> bterms;
  std::size_t terms_size = terms.size();
  bterms.reserve(terms_size);
  for (auto && t : terms)
  {
    bterms.push_back(std::static_pointer_cast<BzlaTerm>(t)->term);
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
        { std::static_pointer_cast<BzlaTerm>(elem.first)->term,
          std::static_pointer_cast<BzlaTerm>(elem.second)->term });
  }
  tm->substitute_terms(bterms, substitution_bterms_map);

  TermVec res;
  res.reserve(terms_size);
  for (auto && t : bterms)
  {
    res.push_back(std::make_shared<BzlaTerm>(t));
  }
  return res;
}

void BzlaSolver::dump_smt2(std::string filename) const
{
  std::ofstream out(filename);
  get_bitwuzla()->print_formula(out, "smt2");
}

BzlaInterpolatingSolver::BzlaInterpolatingSolver()
    : AbsSmtInterpolator(BZLA_INTERPOLATOR, std::make_shared<BzlaSolver>()),
      bzla_solver(std::static_pointer_cast<BzlaSolver>(backend_solver))
{
  initialize();
}

void BzlaInterpolatingSolver::initialize()
{
  if (!bzla_solver->is_initialized())
  {
    bzla_solver->set_opt("produce-interpolants", "true");
  }
}

void BzlaInterpolatingSolver::set_opt(const std::string option,
                                      const std::string value)
{
  if (disallowed_options.find(option) != disallowed_options.end())
  {
    throw IncorrectUsageException(
        "Bitwuzla interpolator does not allow option: " + option);
  }
  if (option == "incremental")
  {
    // Bitwuzla itself does not distinguish between incremental and
    // non-incremental solving. However, we use this option to determine whether
    // we want to reuse assertions on the solver stack between interpolation
    // queries.
    if (value == "true" || value == "1")
    {
      incremental_mode = true;
    }
    else if (value == "false" || value == "0")
    {
      incremental_mode = false;
    }
    else
    {
      throw IncorrectUsageException(
          "Invalid value for boolean option 'incremental'");
    }
    return;
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
  if (!incremental_mode)
  {
    last_itp_query_assertions.clear();
  }

  // count how many assertions can be reused
  size_t num_reused = 0;
  while (num_reused < last_itp_query_assertions.size()
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
    bzla_solver->get_bitwuzla()->assert_formula(
        std::static_pointer_cast<BzlaTerm>(formulae.at(k))->term);
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
    partitions.push_back(
        { std::static_pointer_cast<BzlaTerm>(formulae.at(i))->term });
  }
  const std::vector<bitwuzla::Term> itps =
      bzla_solver->get_bitwuzla()->get_interpolants(partitions);
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
      out_I.push_back(std::make_shared<BzlaTerm>(itp));
    }
  }

  assert(out_I.size() == formulae.size() - 1);
  return r;
}

void BzlaInterpolatingSolver::reset_assertions()
{
  bzla_solver->reset_assertions();
  last_itp_query_assertions.clear();
  initialize();
}

void BzlaInterpolatingSolver::reset()
{
  // these terms belong to the term manager bzla_solver->reset() destroys
  last_itp_query_assertions.clear();
  bzla_solver->reset();
  initialize();
}

}  // namespace smt
