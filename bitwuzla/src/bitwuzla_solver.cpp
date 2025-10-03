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

void BzlaSolver::set_opt(const std::string option, const std::string value)
{
  if (option == "incremental")
  {
    // Bitwuzla does not distinguish between incremental and non-incremental
    // solving.
    return;
  }
  else if (option == "time-limit")
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

void BzlaSolver::set_logic(const std::string logic)
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
    Assert(r == bitwuzla::Result::UNKNOWN);
    return Result(UNKNOWN);
  }
}

Result BzlaSolver::check_sat_assuming(const TermVec & assumptions)
{
  return check_sat_assuming_internal(assumptions);
}

Result BzlaSolver::check_sat_assuming_list(const TermList & assumptions)
{
  return check_sat_assuming_internal(assumptions);
}

Result BzlaSolver::check_sat_assuming_set(const UnorderedTermSet & assumptions)
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
  throw NotImplementedException(
      "Bitwuzla backend does not support uninterpreted sorts");
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

Sort BzlaSolver::make_sort(SortKind sk, const Sort & sort1) const
{
  throw IncorrectUsageException(
      "Bitwuzla has no sort that takes a single sort argument.");
}

Sort BzlaSolver::make_sort(SortKind sk,
                           const Sort & sort1,
                           const Sort & sort2) const
{
  std::shared_ptr<BzlaSort> bsort1 = std::static_pointer_cast<BzlaSort>(sort1);
  std::shared_ptr<BzlaSort> bsort2 = std::static_pointer_cast<BzlaSort>(sort2);

  if (sk == ARRAY)
  {
    return std::make_shared<BzlaSort>(
        tm->mk_array_sort(bsort1->sort, bsort2->sort));
  }
  else if (sk == FUNCTION)
  {
    std::vector<bitwuzla::Sort> domain_sorts({ bsort1->sort });
    return std::make_shared<BzlaSort>(
        tm->mk_fun_sort(domain_sorts, bsort2->sort));
  }
  else
  {
    std::string msg("Can't create sort from sort kind ");
    msg += to_string(sk);
    msg += " with two sort arguments.";
    throw IncorrectUsageException(msg);
  }
}

Sort BzlaSolver::make_sort(SortKind sk,
                           const Sort & sort1,
                           const Sort & sort2,
                           const Sort & sort3) const
{
  std::shared_ptr<BzlaSort> bsort1 = std::static_pointer_cast<BzlaSort>(sort1);
  std::shared_ptr<BzlaSort> bsort2 = std::static_pointer_cast<BzlaSort>(sort2);
  std::shared_ptr<BzlaSort> bsort3 = std::static_pointer_cast<BzlaSort>(sort3);

  if (sk == FUNCTION)
  {
    return std::make_shared<BzlaSort>(
        tm->mk_fun_sort({ bsort1->sort, bsort2->sort }, bsort3->sort));
  }
  else
  {
    throw IncorrectUsageException(
        "Bitwuzla does not have a non-function sort that takes three sort "
        "arguments");
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
  else if (sorts.size() == 1)
  {
    return make_sort(sk, sorts[0]);
  }
  else if (sorts.size() == 2)
  {
    return make_sort(sk, sorts[0], sorts[1]);
  }
  else if (sorts.size() == 3)
  {
    return make_sort(sk, sorts[0], sorts[1], sorts[2]);
  }
  else
  {
    std::string msg("Can't create sort from sort kind ");
    msg += to_string(sk);
    msg += " with a vector of sorts";
    throw IncorrectUsageException(msg);
  }
}

Sort BzlaSolver::make_sort(const Sort & sort_con, const SortVec & sorts) const

{
  throw IncorrectUsageException(
      "Bitwuzla does not support uninterpreted sort construction");
}

Sort BzlaSolver::make_sort(const DatatypeDecl & d) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

DatatypeDecl BzlaSolver::make_datatype_decl(const std::string & s)
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

DatatypeConstructorDecl BzlaSolver::make_datatype_constructor_decl(
    const std::string s)
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

void BzlaSolver::add_constructor(DatatypeDecl & dt,
                                 const DatatypeConstructorDecl & con) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

void BzlaSolver::add_selector(DatatypeConstructorDecl & dt,
                              const std::string & name,
                              const Sort & s) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

void BzlaSolver::add_selector_self(DatatypeConstructorDecl & dt,
                                   const std::string & name) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

Term BzlaSolver::get_constructor(const Sort & s, std::string name) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

Term BzlaSolver::get_tester(const Sort & s, std::string name) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

Term BzlaSolver::get_selector(const Sort & s,
                              std::string con,
                              std::string name) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
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
  return std::make_shared<BzlaTerm>(tm->mk_bv_value(bsort->sort, val, base));
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
    Assert(op.num_idx == 2);
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
    Assert(op.num_idx == 2);
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
    Assert(op.num_idx > 0 && op.num_idx <= 1);
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
    Assert(op.num_idx > 0 && op.num_idx <= 2);
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
  throw NotImplementedException("Bitwuzla does not currently support reset");
}

void BzlaSolver::reset_assertions()
{
  delete bzla;
  bzla = new bitwuzla::Bitwuzla(*tm, options);
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
  super::set_opt(option, value);
}

void BzlaInterpolatingSolver::push(uint64_t num)
{
  throw IncorrectUsageException("Can't call push from interpolating solver");
}

void BzlaInterpolatingSolver::pop(uint64_t num)
{
  throw IncorrectUsageException("Can't call pop from interpolating solver");
}

void BzlaInterpolatingSolver::assert_formula(const Term & t)
{
  throw IncorrectUsageException(
      "Can't assert formulas in interpolating solver");
}

Result BzlaInterpolatingSolver::check_sat()
{
  throw IncorrectUsageException(
      "Can't call check_sat from interpolating solver");
}

Result BzlaInterpolatingSolver::check_sat_assuming(const TermVec & assumptions)
{
  throw IncorrectUsageException(
      "Can't call check_sat_assuming from interpolating solver");
}

Term BzlaInterpolatingSolver::get_value(const Term & t) const
{
  throw IncorrectUsageException("Can't get values from interpolating solver");
}

// delegate the interpolation procedure to `get_sequence_interpolants`
Result BzlaInterpolatingSolver::get_interpolant(const Term & A,
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

Result BzlaInterpolatingSolver::get_sequence_interpolants(
    const TermVec & formulae, TermVec & out_I) const
{
  if (formulae.size() < 2)
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
  get_bitwuzla()->pop(last_itp_query_assertions.size() - num_reused);

  // update the interpolation groups and assertions
  last_itp_query_assertions.resize(num_reused);
  last_itp_query_assertions.reserve(formulae.size());

  // add new assertions from formulas
  for (size_t k = num_reused; k < formulae.size(); ++k)
  {
    // Add a new backtrack point and push the formula.
    get_bitwuzla()->push(1);
    get_bitwuzla()->assert_formula(
        std::static_pointer_cast<BzlaTerm>(formulae.at(k))->term);
    last_itp_query_assertions.push_back(formulae.at(k));
  }
  assert(formulae == last_itp_query_assertions);

  if (!dump_queries_prefix.empty())
  {
    // Note: the dumped query will only include the current assertions
    std::ofstream out(dump_queries_prefix + "."
                      + std::to_string(itp_query_count) + ".smt2");
    get_bitwuzla()->print_formula(out, "smt2");
    out.close();
  }
  itp_query_count++;

  // solve query and get interpolants
  bitwuzla::Result bzla_res;
  try
  {
    bzla_res = get_bitwuzla()->check_sat();
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
  for (size_t i = 1; i < formulae.size(); ++i)
  {
    std::vector<bitwuzla::Term> partition;
    partition.reserve(i);
    for (size_t j = 0; j < i; ++j)
    {
      partition.push_back(
          std::static_pointer_cast<BzlaTerm>(formulae.at(j))->term);
    }
    bitwuzla::Term itp = get_bitwuzla()->get_interpolant(partition);
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
  super::reset_assertions();
  last_itp_query_assertions.clear();
}

void BzlaInterpolatingSolver::reset()
{
  super::reset();
  last_itp_query_assertions.clear();
}

}  // namespace smt
