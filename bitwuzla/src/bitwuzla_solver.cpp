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

using namespace std;

namespace smt {

const std::unordered_map<PrimOp, BitwuzlaKind> op2bkind(
    { /* Core Theory */
      { And, BITWUZLA_KIND_AND },
      { Or, BITWUZLA_KIND_OR },
      { Xor, BITWUZLA_KIND_XOR },
      { Not, BITWUZLA_KIND_NOT },
      // needs to be translated
      { Implies, BITWUZLA_KIND_IMPLIES },
      { Iff, BITWUZLA_KIND_IFF },
      { Ite, BITWUZLA_KIND_ITE },
      { Equal, BITWUZLA_KIND_EQUAL },
      { Distinct, BITWUZLA_KIND_DISTINCT },
      /* Uninterpreted Functions */
      { Apply, BITWUZLA_KIND_APPLY },
      /* Fixed Size BitVector Theory */
      { Concat, BITWUZLA_KIND_BV_CONCAT },
      { Extract, BITWUZLA_KIND_BV_EXTRACT },  // Indexed
      { BVNot, BITWUZLA_KIND_BV_NOT },
      { BVNeg, BITWUZLA_KIND_BV_NEG },
      { BVAnd, BITWUZLA_KIND_BV_AND },
      { BVOr, BITWUZLA_KIND_BV_OR },
      { BVXor, BITWUZLA_KIND_BV_XOR },
      { BVNand, BITWUZLA_KIND_BV_NAND },
      { BVNor, BITWUZLA_KIND_BV_NOR },
      { BVXnor, BITWUZLA_KIND_BV_XNOR },
      { BVAdd, BITWUZLA_KIND_BV_ADD },
      { BVSub, BITWUZLA_KIND_BV_SUB },
      { BVMul, BITWUZLA_KIND_BV_MUL },
      { BVUdiv, BITWUZLA_KIND_BV_UDIV },
      { BVSdiv, BITWUZLA_KIND_BV_SDIV },
      { BVUrem, BITWUZLA_KIND_BV_UREM },
      { BVSrem, BITWUZLA_KIND_BV_SREM },
      { BVSmod, BITWUZLA_KIND_BV_SMOD },
      { BVShl, BITWUZLA_KIND_BV_SHL },
      { BVAshr, BITWUZLA_KIND_BV_ASHR },
      { BVLshr, BITWUZLA_KIND_BV_SHR },
      { BVComp, BITWUZLA_KIND_BV_COMP },
      { BVUlt, BITWUZLA_KIND_BV_ULT },
      { BVUle, BITWUZLA_KIND_BV_ULE },
      { BVUgt, BITWUZLA_KIND_BV_UGT },
      { BVUge, BITWUZLA_KIND_BV_UGE },
      { BVSlt, BITWUZLA_KIND_BV_SLT },
      { BVSle, BITWUZLA_KIND_BV_SLE },
      { BVSgt, BITWUZLA_KIND_BV_SGT },
      { BVSge, BITWUZLA_KIND_BV_SGE },
      { Zero_Extend, BITWUZLA_KIND_ZERO_EXTEND },  // Indexed
      { Sign_Extend, BITWUZLA_KIND_SIGN_EXTEND },  // Indexed
      { Repeat, BITWUZLA_KIND_REPEAT },            // Indexed
      { Rotate_Left, BITWUZLA_KIND_ROLI },         // Indexed
      { Rotate_Right, BITWUZLA_KIND_RORI },        // Indexed
      /* Array Theory */
      { Select, BITWUZLA_KIND_ARRAY_SELECT },
      { Store, BITWUZLA_KIND_ARRAY_STORE },
      /* Quantifiers */
      { Forall, BITWUZLA_KIND_FORALL },
      { Exists, BITWUZLA_KIND_EXISTS } });

void BzlaSolver::set_opt(const string option, const string value)
{
  // TODO support more options
  if (option == "incremental")
  {
    bitwuzla_set_option(bzla, BITWUZLA_OPT_INCREMENTAL, (value == "true"));
  }
  else if (option == "produce-models")
  {
    bitwuzla_set_option(bzla, BITWUZLA_OPT_PRODUCE_MODELS, (value == "true"));
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
  bitwuzla_assert(bzla, bterm->term);
}

Result BzlaSolver::check_sat()
{
  BitwuzlaResult r = bitwuzla_check_sat(bzla);
  if (r == BITWUZLA_SAT)
  {
    return Result(SAT);
  }
  else if (r == BITWUZLA_UNSAT)
  {
    return Result(UNSAT);
  }
  else
  {
    assert(r == BITWUZLA_UNKNOWN);
    return Result(UNKNOWN);
  }
}

Result BzlaSolver::check_sat_assuming(const TermVec & assumptions)
{
  // TODO need to check they're all literals
  throw NotImplementedException("");
}

void BzlaSolver::push(uint64_t num) { bitwuzla_push(bzla, num); }

void BzlaSolver::pop(uint64_t num) { bitwuzla_pop(bzla, num); }

Term BzlaSolver::get_value(const Term & t) const
{
  shared_ptr<BzlaTerm> bterm = static_pointer_cast<BzlaTerm>(t);
  return make_shared<BzlaTerm>(bitwuzla_get_value(bzla, bterm->term));
}

UnorderedTermMap BzlaSolver::get_array_values(const Term & arr,
                                              Term & out_const_base) const
{
  throw NotImplementedException(
      "Bitwuzla backend doesn't support get_array_values yet");
}

void BzlaSolver::get_unsat_core(UnorderedTermSet & out)
{
  const BitwuzlaTerm ** bcore = bitwuzla_get_unsat_core(bzla);
  while (*bcore)
  {
    out.insert(make_shared<BzlaTerm>(*bcore));
    bcore++;
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
    return make_shared<BzlaSort>(bitwuzla_mk_bool_sort(bzla));
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
    return make_shared<BzlaSort>(bitwuzla_mk_bv_sort(bzla, size));
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
  shared_ptr<BzlaSort> bsort1 = static_pointer_cast<BzlaSort>(sort1);
  shared_ptr<BzlaSort> bsort2 = static_pointer_cast<BzlaSort>(sort2);

  if (sk == ARRAY)
  {
    return make_shared<BzlaSort>(
        bitwuzla_mk_array_sort(bzla, bsort1->sort, bsort2->sort));
  }
  else if (sk == FUNCTION)
  {
    vector<BitwuzlaSort *> domain_sorts({ bsort1->sort });
    return make_shared<BzlaSort>(bitwuzla_mk_fun_sort(
        bzla, domain_sorts.size(), &domain_sorts[0], bsort2->sort));
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
    vector<BitwuzlaSort *> domain_sorts({ bsort1->sort, bsort2->sort });
    return make_shared<BzlaSort>(bitwuzla_mk_fun_sort(
        bzla, domain_sorts.size(), &domain_sorts[0], bsort3->sort));
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
    std::shared_ptr<BzlaSort *> bzla_return_sort =
        std::static_pointer_cast<BzlaSort *>(returnsort);

    // arity is one less, because last sort is return sort
    uint32_t arity = sorts.size() - 1;
    std::vector<BoolectorSort> bzla_sorts;
    bzla_sorts.reserve(arity);
    for (size_t i = 0; i < arity; i++)
    {
      std::shared_ptr<BzlaSort *> bs =
          std::static_pointer_cast<BzlaSort *>(sorts[i]);
      bzla_sorts.push_back(bs->sort);
    }

    return std::make_shared<BzlaSort>(
        bitwuzla_fun_sort(bzla, arity, &bzla_sorts[0], bzla_return_sort->sort));
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
    std::string msg("Can't create sort from sort constructor ");
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
    return shared_ptr<BzlaTerm>(bitwuzla_make_true(bzla));
  }
  else
  {
    return shared_ptr<BzlaTerm>(bitwuzla_make_false(bzla));
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
  return make_shared<BzlaTerm>(
      bitwuzla_make_bv_value_uint64_t(bzla, bsort->sort));
}

Term BzlaSolver::make_term(const std::string val,
                           const Sort & sort,
                           uint64_t base = 10) const
{
  SortKind sk = sort->get_sort_kind();
  if (sk != BV)
  {
    throw NotImplementedException(
        "Bitwuzla does not support creating values for sort kind"
        + to_string(sk));
  }

  shared_ptr<BzlaSort> bsort = static_pointer_cast<BzlaSort>(sort);
  return make_shared<BzlaTerm>(
      bitwuzla_mk_bv_value(bzla, bsort->sort, val.c_str(), base));
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
  else if (val != sort->get_elemsort())
  {
    throw IncorrectUsageException(
        "Value used to create constant array must match element sort.");
  }

  shared_ptr<BzlaTerm> bterm = static_pointer_cast<BzlaTerm>(term);
  shared_ptr<BzlaSort> bsort = static_pointer_cast<BzlaSort>(sort);
  return make_shared<BzlaTerm>(
      bitwuzla_mk_const_array(bzla, bsort->sort, bterm->term));
}

Term BzlaSolver::make_symbol(const string name, const Sort & sort)
{
  shared_ptr<BzlaSort> bsort = static_pointer_cast<BzlaSort>(sort);
  return make_shared<BzlaTerm>(
      bitwuzla_mk_const(bzla, bsort->sort, name.c_str()));
}

Term BzlaSolver::make_param(const std::string name, const Sort & sort)
{
  shared_ptr<BzlaSort> bsort = static_pointer_cast<BzlaSort>(sort);
  return make_shared<BzlaTerm>(
      bitwuzla_mk_var(bzla, bsort->sort, name.c_str()));
}

Term BzlaSolver::make_term(Op op, const Term & t) const
{
  shared_ptr<BzlaTerm> bterm = static_pointer_cast<BzlaTerm>(t);

  auto it = op2bkind.find(op.prim_op);
  if (it == op2bkind.end())
  {
    throw IncorrectUsageException("Bitwuzla does not yet support operator: "
                                  + to_string(op));
  }
  BitwuzlaKind bkind = *it;

  if (!op.num_idx)
  {
    return make_shared<BzlaTerm>(bitwuzla_mk_term1(bzla, bkind, bterm->term));
  }
  else if (op.num_idx == 1)
  {
    return make_shared<BzlaTerm>(
        bitwuzla_mk_term1_indexed1(bzla, bkind, bterm->term, op.idx0));
  }
  else
  {
    assert(op.num_idx == 2);
    return make_shared<BzlaTerm>(
        bitwuzla_mk_term1_indexed2(bzla, bkind, bterm->term, op.idx0, op.idx1));
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
                                  + to_string(op));
  }
  BitwuzlaKind bkind = *it;

  if (!op.num_idx)
  {
    return make_shared<BzlaTerm>(
        bitwuzla_mk_term2(bzla, bkind, bterm0->term, bterm1->term));
  }
  else if (op.num_idx == 1)
  {
    return make_shared<BzlaTerm>(bitwuzla_mk_term2_indexed1(
        bzla, bkind, bterm0->term, bterm1->term, op.idx0));
  }
  else
  {
    assert(op.num_idx == 2);
    return make_shared<BzlaTerm>(bitwuzla_mk_term2_indexed2(
        bzla, bkind, bterm0->term, bterm1->term, op.idx0, op.idx1));
  }
}

Term BzlaSolver::make_term(Op op,
                           const Term & t0,
                           const Term & t1,
                           const Term & t2) const
{
  shared_ptr<BzlaTerm> bterm0 = static_pointer_cast<BzlaTerm>(t0);
  shared_ptr<BzlaTerm> bterm1 = static_pointer_cast<BzlaTerm>(t1);
  shared_ptr<BzlaTerm> bterm2 = static_pointer_cast<BzlaTerm>(t2);

  auto it = op2bkind.find(op.prim_op);
  if (it == op2bkind.end())
  {
    throw IncorrectUsageException("Bitwuzla does not yet support operator: "
                                  + to_string(op));
  }
  BitwuzlaKind bkind = *it;

  if (!op.num_idx)
  {
    return make_shared<BzlaTerm>(bitwuzla_mk_term3(
        bzla, bkind, bterm0->term, bterm1->term, bterm2->term));
  }
  else if (op.num_idx == 1)
  {
    return make_shared<BzlaTerm>(bitwuzla_mk_term3_indexed1(
        bzla, bkind, bterm0->term, bterm1->term, bterm2->term, op.idx0));
  }
  else
  {
    assert(op.num_idx == 2);
    return make_shared<BzlaTerm>(bitwuzla_mk_term3_indexed2(bzla,
                                                            bkind,
                                                            bterm0->term,
                                                            bterm1->term,
                                                            bterm2->term,
                                                            op.idx0,
                                                            op.idx1));
  }
}

Term BzlaSolver::make_term(Op op, const TermVec & terms) const
{
  vector<BitwuzlaTerm *> bitwuzla_terms;
  for (auto t : terms)
  {
    bitwuzla_terms.push_back(static_pointer_cast<BzlaTerm>(t)->term);
  }

  auto it = op2bkind.find(op.prim_op);
  if (it == op2bkind.end())
  {
    throw IncorrectUsageException("Bitwuzla does not yet support operator: "
                                  + to_string(op));
  }
  BitwuzlaKind bkind = *it;

  if (!op.num_idx)
  {
    return make_shared < BzlaTerm(bitwuzla_mk_term(
               bzla, bkind, bitwuzla_terms.size(), &bitwuzla_terms[0]));
  }
  else
  {
    assert(op.num_idx > 0 && op.num_idx <= 1);
    vector<uint32_t> indices({ op.idx0 });
    if (op.num_idx == 2)
    {
      indices.push_back(op.idx1);
    }
    return make_shared<BzlaTerm>(bitwuzla_mk_term_indexed(bzla,
                                                          bkind,
                                                          bitwuzla_terms.size(),
                                                          &bitwuzla_terms[0],
                                                          indices.size(),
                                                          &indices[0]));
  }
}

void BzlaSolver::reset()
{
  // TODO: will it clean up memory automatically on delete?
  bitwuzla_delete(bzla);
  bzla = bitwuzla_new();
}

void BzlaSolver::reset_assertions()
{
  throw NotImplementedException(
      "Bitwuzla does not currently support reset_assertions");
}

void BzlaSolver::dump_smt2(std::string filename) const
{
  FILE * file = fopen(filename.c_str(), "w");
  bitwuzla_dump_formula(bzla, "smt2", file);
  fclose(file);
}

}  // namespace smt
