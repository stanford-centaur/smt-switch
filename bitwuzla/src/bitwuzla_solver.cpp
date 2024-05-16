/*********************                                                        */
/*! \file bitwuzla_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
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
#include "assert.h"
#include "bitwuzla/cpp/bitwuzla.h"

using namespace std;

namespace smt {
bitwuzla::Bitwuzla * running_bzla = nullptr;  ///< used for calling terminate
                                    ///< if a time limit is reached

void bzla_timelimit_handler(int signum)
{
  // assert(running_bzla != nullptr);
  // void * state = bitwuzla_get_termination_callback_state(running_bzla);
  // bool * statebool = reinterpret_cast<bool *>(state);
  // *statebool = true;
  // bitwuzla_terminate(running_bzla);
}

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

const unordered_map<uint64_t, uint64_t> bvbasemap(
    { { 2, 2 },
      { 10, 10 },
      { 16, 16 } });

void BzlaSolver::set_opt(const string option, const string value)
{
  // TODO support more options
  if (option == "incremental")
  {

  }
  else if (option == "produce-models")
  {
    options.set(bitwuzla::Option::PRODUCE_MODELS, true);
  }
  else if (option == "produce-unsat-assumptions")
  {
    options.set(bitwuzla::Option::PRODUCE_UNSAT_ASSUMPTIONS, true);
  }
  else if (option == "produce-unsat-cores")
  {
    options.set(bitwuzla::Option::PRODUCE_UNSAT_CORES, true);
  }
  else if (option == "time-limit")
  {
    time_limit = stoi(value);
  }
  else
  {
    throw SmtException("Bitwuzla backend does not support option: " + option);
  }
}

void BzlaSolver::set_logic(const string logic)
{
  // no need to set logic in bitwuzla
  return;
}

void BzlaSolver::assert_formula(const Term & t)
{
  shared_ptr<BzlaTerm> bterm = static_pointer_cast<BzlaTerm>(t);
  get_bzla()->assert_formula(bterm->term);
}

Result BzlaSolver::check_sat()
{
  timelimit_start();
  bitwuzla::Result r = get_bzla()->check_sat();
  bool tl_triggered = timelimit_end();
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
    if (tl_triggered)
    {
      return Result(UNKNOWN, "Time limit reached.");
    }
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

void BzlaSolver::push(uint64_t num)
{
  get_bzla()->push(num);
  context_level += num;
}

void BzlaSolver::pop(uint64_t num)
{
  get_bzla()->pop(num);
  context_level -= num;
}

uint64_t BzlaSolver::get_context_level() const { return context_level; }

Term BzlaSolver::get_value(const Term & t) const
{
  shared_ptr<BzlaTerm> bterm = static_pointer_cast<BzlaTerm>(t);
  return make_shared<BzlaTerm>(get_bzla()->get_value(bterm->term));
}

UnorderedTermMap BzlaSolver::get_array_values(const Term & arr,
                                              Term & out_const_base) const
{
  throw NotImplementedException(
      "Bitwuzla backend doesn't support get_array_values yet");
}

void BzlaSolver::get_unsat_assumptions(UnorderedTermSet & out)
{
  try
  {
    std::vector<bitwuzla::Term> bcore = get_bzla()->get_unsat_assumptions();
    for (auto&& elt: bcore)
    {
      out.insert(make_shared<BzlaTerm>(elt));
    }
    // assert(out.size() > 1);
  }
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort BzlaSolver::make_sort(const string name, uint64_t arity) const
{
  throw NotImplementedException(
      "Bitwuzla backend does not support uninterpreted sorts");
}

Sort BzlaSolver::make_sort(SortKind sk) const
{
  if (sk == BOOL)
  {
    return make_shared<BzlaSort>(tm->mk_bool_sort());
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
    return make_shared<BzlaSort>(tm->mk_bv_sort(size));
  }
  else
  {
    std::string msg("Can't create sort from sort kind");
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
  shared_ptr<BzlaSort> bsort1 = static_pointer_cast<BzlaSort>(sort1);
  shared_ptr<BzlaSort> bsort2 = static_pointer_cast<BzlaSort>(sort2);

  if (sk == ARRAY)
  {
    return make_shared<BzlaSort>(tm->mk_array_sort(bsort1->sort, bsort2->sort));
  }
  else if (sk == FUNCTION)
  {
    vector<bitwuzla::Sort> domain_sorts({ bsort1->sort });
    return make_shared<BzlaSort>(tm->mk_fun_sort(
        domain_sorts, bsort2->sort));
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
  shared_ptr<BzlaSort> bsort1 = static_pointer_cast<BzlaSort>(sort1);
  shared_ptr<BzlaSort> bsort2 = static_pointer_cast<BzlaSort>(sort2);
  shared_ptr<BzlaSort> bsort3 = static_pointer_cast<BzlaSort>(sort3);

  if (sk == FUNCTION)
  {
    const vector<bitwuzla::Sort> domain_sorts({ bsort1->sort, bsort2->sort });
    return make_shared<BzlaSort>(tm->mk_fun_sort(domain_sorts, bsort3->sort));
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
    uint32_t arity = sorts.size() - 1;
    std::vector<bitwuzla::Sort> bzla_sorts;
    bzla_sorts.reserve(arity);
    for (size_t i = 0; i < arity; i++)
    {
      std::shared_ptr<BzlaSort> bs =
          std::static_pointer_cast<BzlaSort>(sorts[i]);
      bzla_sorts.push_back(bs->sort);
    }

    return std::make_shared<BzlaSort>(tm->mk_fun_sort(bzla_sorts, {bzla_return_sort->sort}));
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

DatatypeDecl BzlaSolver::make_datatype_decl(const string & s)
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

DatatypeConstructorDecl BzlaSolver::make_datatype_constructor_decl(
    const string s)
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

void BzlaSolver::add_constructor(DatatypeDecl & dt,
                                 const DatatypeConstructorDecl & con) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

void BzlaSolver::add_selector(DatatypeConstructorDecl & dt,
                              const string & name,
                              const Sort & s) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

void BzlaSolver::add_selector_self(DatatypeConstructorDecl & dt,
                                   const string & name) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

Term BzlaSolver::get_constructor(const Sort & s, string name) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

Term BzlaSolver::get_tester(const Sort & s, string name) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

Term BzlaSolver::get_selector(const Sort & s, string con, string name) const
{
  throw IncorrectUsageException("Bitwuzla does not support datatypes.");
}

Term BzlaSolver::make_term(bool b) const
{
  if (b)
  {
    return make_shared<BzlaTerm>(tm->mk_true());
  }
  else
  {
    return make_shared<BzlaTerm>(tm->mk_false());
  }
}

Term BzlaSolver::make_term(int64_t i, const Sort & sort) const
{
  SortKind sk = sort->get_sort_kind();
  if (sk != BV)
  {
    throw NotImplementedException(
        "Bitwuzla does not support creating values for sort kind"
        + to_string(sk));
  }

  shared_ptr<BzlaSort> bsort = static_pointer_cast<BzlaSort>(sort);
  return make_shared<BzlaTerm>(tm->mk_bv_value_uint64(bsort->sort, i));
}

Term BzlaSolver::make_term(const std::string val,
                           const Sort & sort,
                           uint64_t base) const
{
  SortKind sk = sort->get_sort_kind();
  if (sk != BV)
  {
    throw NotImplementedException(
        "Bitwuzla does not support creating values for sort kind"
        + to_string(sk));
  }

  auto baseit = bvbasemap.find(base);
  if (baseit == bvbasemap.end())
  {
    throw IncorrectUsageException(::std::to_string(base) + " base for creating a BV value is not supported."
                                  " Options are 2, 10, and 16");
  }

  shared_ptr<BzlaSort> bsort = static_pointer_cast<BzlaSort>(sort);
  return make_shared<BzlaTerm>(tm->mk_bv_value(bsort->sort, val.c_str(), baseit->second));
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

  shared_ptr<BzlaTerm> bterm = static_pointer_cast<BzlaTerm>(val);
  shared_ptr<BzlaSort> bsort = static_pointer_cast<BzlaSort>(sort);
  return make_shared<BzlaTerm>(tm->mk_const_array(bsort->sort, bterm->term));
}

Term BzlaSolver::make_symbol(const string name, const Sort & sort)
{
  if (symbol_table.find(name) != symbol_table.end())
  {
    throw IncorrectUsageException("Symbol name " + name + " already used.");
  }
  shared_ptr<BzlaSort> bsort = static_pointer_cast<BzlaSort>(sort);
  Term sym = make_shared<BzlaTerm>(tm->mk_const(bsort->sort, name));
  symbol_table[name] = sym;
  return sym;
}

Term BzlaSolver::get_symbol(const string & name)
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
  shared_ptr<BzlaSort> bsort = static_pointer_cast<BzlaSort>(sort);
  return make_shared<BzlaTerm>(tm->mk_var(bsort->sort, name));
}

Term BzlaSolver::make_term(Op op, const Term & t) const
{
  shared_ptr<BzlaTerm> bterm = static_pointer_cast<BzlaTerm>(t);

  auto it = op2bkind.find(op.prim_op);
  if (it == op2bkind.end())
  {
    throw IncorrectUsageException("Bitwuzla does not yet support operator: "
                                  + op.to_string());
  }
  bitwuzla::Kind bkind = it->second;

  if (!op.num_idx)
  {
    return make_shared<BzlaTerm>(tm->mk_term( bkind, {bterm->term}));
  }
  else if (op.num_idx == 1)
  {
    return make_shared<BzlaTerm>(
        tm->mk_term(bkind, {bterm->term}, {op.idx0}));
  }
  else
  {
    assert(op.num_idx == 2);
    return make_shared<BzlaTerm>(tm->mk_term(bkind, {bterm->term}, {op.idx0, op.idx1}));
  }
}

Term BzlaSolver::make_term(Op op, const Term & t0, const Term & t1) const
{
  shared_ptr<BzlaTerm> bterm0 = static_pointer_cast<BzlaTerm>(t0);
  shared_ptr<BzlaTerm> bterm1 = static_pointer_cast<BzlaTerm>(t1);

  auto it = op2bkind.find(op.prim_op);
  if (it == op2bkind.end())
  {
    throw IncorrectUsageException("Bitwuzla does not yet support operator: "
                                  + op.to_string());
  }
  bitwuzla::Kind bkind = it->second;

  if (!op.num_idx)
  {
    return make_shared<BzlaTerm>(
        tm->mk_term(bkind, {bterm0->term, bterm1->term}));
  }
  else if (op.num_idx == 1)
  {
    return make_shared<BzlaTerm>(tm->mk_term(
        bkind, {bterm0->term, bterm1->term}, {op.idx0}));
  }
  else
  {
    assert(op.num_idx == 2);
    return make_shared<BzlaTerm>(tm->mk_term(
        bkind, {bterm0->term, bterm1->term}, {op.idx0, op.idx1}));
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
    return make_term(op, {t0, t1, t2});
  }

  shared_ptr<BzlaTerm> bterm0 = static_pointer_cast<BzlaTerm>(t0);
  shared_ptr<BzlaTerm> bterm1 = static_pointer_cast<BzlaTerm>(t1);
  shared_ptr<BzlaTerm> bterm2 = static_pointer_cast<BzlaTerm>(t2);

  auto it = op2bkind.find(op.prim_op);
  if (it == op2bkind.end())
  {
    throw IncorrectUsageException("Bitwuzla does not yet support operator: "
                                  + op.to_string());
  }
  bitwuzla::Kind bkind = it->second;

  if (!op.num_idx)
  {
    return make_shared<BzlaTerm>(tm->mk_term(
        bkind, {bterm0->term, bterm1->term, bterm2->term}));
  }
  else
  {
    assert(op.num_idx > 0 && op.num_idx <= 1);
    const vector<bitwuzla::Term> bitwuzla_terms(
        { bterm0->term, bterm1->term, bterm2->term });
    vector<uint64_t> indices({ (uint32_t)op.idx0 });
    if (op.num_idx == 2)
    {
      indices.push_back(op.idx1);
    }

    return make_shared<BzlaTerm>(tm->mk_term(bkind, bitwuzla_terms, indices));
  }
}

Term BzlaSolver::make_term(Op op, const TermVec & terms) const
{
  std::vector<bitwuzla::Term> bitwuzla_terms;
  for (auto t : terms)
  {
    bitwuzla_terms.push_back(static_pointer_cast<BzlaTerm>(t)->term);
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
    return make_shared<BzlaTerm>(tm->mk_term(
        bkind, bitwuzla_terms));
  }
  else
  {
    assert(op.num_idx > 0 && op.num_idx <= 2);
    vector<uint64_t> indices({ (uint64_t)op.idx0 });
    if (op.num_idx == 2)
    {
      indices.push_back(op.idx1);
    }
    return make_shared<BzlaTerm>(tm->mk_term(bkind, bitwuzla_terms, indices));
  }
}

void BzlaSolver::reset()
{
throw NotImplementedException(
      "Bitwuzla does not currently support reset");
}

void BzlaSolver::reset_assertions()
{
  throw NotImplementedException(
      "Bitwuzla does not currently support reset_assertions");
}

Term BzlaSolver::substitute(const Term term,
                            const UnorderedTermMap & substitution_map) const
{
  // shared_ptr<BzlaTerm> bterm = static_pointer_cast<BzlaTerm>(term);
  // size_t smap_size = substitution_map.size();
  // vector<const BzlaTerm *> map_keys;
  // map_keys.reserve(smap_size);
  // vector<const bitwuzla::Term *> map_vals;
  // map_keys.reserve(smap_size);
  // for (auto elem : substitution_map)
  // {
  //   if (!elem.first->is_symbolic_const() && !elem.first->is_param())
  //   {
  //     throw SmtException(
  //         "Bitwuzla backend doesn't support substitution with non symbol keys");
  //   }
  //   map_keys.push_back(static_pointer_cast<BzlaTerm>(elem.first)->term);
  //   map_vals.push_back(static_pointer_cast<BzlaTerm>(elem.second)->term);
  // }
  // return make_shared<BzlaTerm>(bitwuzla_substitute_term(
  //     bzla, bterm->term, map_keys.size(), map_keys.data(), map_vals.data()));
    throw SmtException(
          "Bitwuzla backend doesn't support substitution");
}

TermVec BzlaSolver::substitute_terms(
    const TermVec & terms, const UnorderedTermMap & substitution_map) const
{
  // size_t terms_size = terms.size();
  // vector<const BitwuzlaTerm *> bterms;
  // bterms.reserve(terms_size);
  // size_t smap_size = substitution_map.size();
  // vector<const BitwuzlaTerm *> map_keys;
  // map_keys.reserve(smap_size);
  // vector<const BitwuzlaTerm *> map_vals;
  // map_keys.reserve(smap_size);
  // for (auto t : terms)
  // {
  //   bterms.push_back(static_pointer_cast<BzlaTerm>(t)->term);
  // }
  // for (auto elem : substitution_map)
  // {
  //   if (!elem.first->is_symbolic_const() && !elem.first->is_param())
  //   {
  //     throw SmtException(
  //         "Bitwuzla backend doesn't support substitution with non symbol keys");
  //   }
  //   map_keys.push_back(static_pointer_cast<BzlaTerm>(elem.first)->term);
  //   map_vals.push_back(static_pointer_cast<BzlaTerm>(elem.second)->term);
  // }

  // // bterms array is updated in place
  // bitwuzla_substitute_terms(bzla,
  //                           terms_size,
  //                           bterms.data(),
  //                           smap_size,
  //                           map_keys.data(),
  //                           map_vals.data());
  // TermVec res;
  // res.reserve(terms_size);
  // for (auto t : bterms)
  // {
  //   res.push_back(make_shared<BzlaTerm>(t));
  // }
  // return res;

  throw SmtException(
        "Bitwuzla backend doesn't support substitution");
}

void BzlaSolver::dump_smt2(std::string filename) const
{
  // FILE * file = fopen(filename.c_str(), "w");
  // bitwuzla_dump_formula(bzla, "smt2", file);
  // fclose(file);
  throw SmtException(
        "Bitwuzla backend doesn't support dump_smt2");
}

// helpers
void BzlaSolver::timelimit_start()
{
  if (time_limit)
  {
    signal(SIGALRM, bzla_timelimit_handler);
    assert(running_bzla == nullptr);
    assert(!terminate_bzla);
    running_bzla = bzla;
    alarm(time_limit);
  }
}

bool BzlaSolver::timelimit_end()
{
  bool res = false;
  if (time_limit)
  {
    res |= terminate_bzla;
    terminate_bzla = false;
    running_bzla = nullptr;
    alarm(0);
  }
  return res;
}

}  // namespace smt
