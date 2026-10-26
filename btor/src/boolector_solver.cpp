/*********************                                                        */
/*! \file boolector_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Boolector implementation of AbsSmtSolver
**
**
**/

#include "boolector_solver.h"

#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <limits>
#include <string>

#include "solver_utils.h"
#include "utils.h"

extern "C" {
#include "btornode.h"
#include "utils/boolectornodemap.h"
}

namespace smt {

/* Boolector op mappings */
// Boolector PrimOp mappings
typedef BoolectorNode * (*un_fun)(Btor *, BoolectorNode *);
typedef BoolectorNode * (*bin_fun)(Btor *, BoolectorNode *, BoolectorNode *);
typedef BoolectorNode * (*tern_fun)(Btor *,
                                    BoolectorNode *,
                                    BoolectorNode *,
                                    BoolectorNode *);

const std::unordered_map<PrimOp, un_fun> unary_ops({ { Not, boolector_not },
                                                     { BVNot, boolector_not },
                                                     { BVNeg,
                                                       boolector_neg } });

// Indexed Operators are implemented inline for make_term
const std::unordered_map<PrimOp, bin_fun> binary_ops(
    { { And, boolector_and },
      { Or, boolector_or },
      { Xor, boolector_xor },
      { Implies, boolector_implies },
      { Equal, boolector_eq },
      { Distinct, boolector_ne },
      { Concat, boolector_concat },
      // Indexed Op: Extract
      { BVAnd, boolector_and },
      { BVOr, boolector_or },
      { BVXor, boolector_xor },
      { BVNand, boolector_nand },
      { BVNor, boolector_nor },
      { BVXnor, boolector_xnor },
      { BVComp, boolector_eq },
      { BVAdd, boolector_add },
      { BVSub, boolector_sub },
      { BVMul, boolector_mul },
      { BVUdiv, boolector_udiv },
      { BVSdiv, boolector_sdiv },
      { BVUrem, boolector_urem },
      { BVSrem, boolector_srem },
      { BVSmod, boolector_smod },
      { BVShl, boolector_sll },
      { BVAshr, boolector_sra },
      { BVLshr, boolector_srl },
      { BVUlt, boolector_ult },
      { BVUle, boolector_ulte },
      { BVUgt, boolector_ugt },
      { BVUge, boolector_ugte },
      { BVSlt, boolector_slt },
      { BVSle, boolector_slte },
      { BVSgt, boolector_sgt },
      { BVSge, boolector_sgte },
      // Indexed Op: Zero_Extend
      // Indexed Op: Sign_Extend
      // Indexed Op: Repeat
      // Indexed Op: Rotate_Left
      // Indexed Op: Rotate_Right
      { Select, boolector_read } });

const std::unordered_map<PrimOp, tern_fun> ternary_ops(
    { { Ite, boolector_cond }, { Store, boolector_write } });

const std::unordered_set<std::string> supported_logics(
    { "QF_BV", "QF_ABV", "QF_UFBV", "QF_AUFBV", "BV", "UFBV", "ABV", "AUFBV" });

/* BoolectorSolver implementation */

// a new Boolector instance, deleted once the solver and every term and sort
// made from it have let go of it
static std::shared_ptr<Btor> new_btor()
{
  return std::shared_ptr<Btor>(boolector_new(), [](Btor * b) {
    boolector_release_all(b);
    boolector_delete(b);
  });
}

BoolectorSolver::BoolectorSolver() : AbsSmtSolver(BTOR), btor(new_btor())
{
  // Boolector exits the process on an abort condition unless given an abort
  // callback, so throw instead. The callback is global, not per instance.
  auto throw_exception = [](const char * msg) -> void {
    throw InternalSolverException(msg);
  };
  boolector_set_abort(throw_exception);
  boolector_set_term(btor.get(), reached_deadline, this);
}

BoolectorSolver::~BoolectorSolver()
{
  // a handle from get_btor() can outlive this solver, so its instance must
  // not call back into it
  boolector_set_term(btor.get(), nullptr, nullptr);
}

std::shared_ptr<Btor> BoolectorSolver::get_btor() { return btor; }

int32_t BoolectorSolver::reached_deadline(void * solver)
{
  const BoolectorSolver * s = static_cast<const BoolectorSolver *>(solver);
  if (s->time_limit == std::chrono::duration<double>::zero())
  {
    return 0;
  }
  return std::chrono::steady_clock::now() >= s->deadline;
}

void BoolectorSolver::set_opt(const std::string option, const std::string value)
{
  if (option == "produce-models")
  {
    if (value == "true")
    {
      boolector_set_opt(btor.get(), BTOR_OPT_MODEL_GEN, 1);
    }
  }
  else if (option == "incremental")
  {
    if (value == "true")
    {
      boolector_set_opt(btor.get(), BTOR_OPT_INCREMENTAL, 1);
    }
  }
  else if (option == "produce-unsat-assumptions")
  {
    if (value == "true")
    {
      // needs to be incremental for getting unsat assumptions
      boolector_set_opt(btor.get(), BTOR_OPT_INCREMENTAL, 1);
    }
  }
  else if (option == "base-context-1" && value == "true")
  {
    base_context_1 = true;
    // pushed directly, so that the context level counts only the caller's
    boolector_push(btor.get(), 1);
  }
  else if (option == "time-limit")
  {
    double seconds = std::stod(value);
    if (seconds < 0)
    {
      throw IncorrectUsageException("time-limit cannot be negative");
    }
    time_limit = std::chrono::duration<double>(seconds);
  }
  else
  {
    // decode the value -- boolector takes a uint32_t val
    uint32_t uint_val;
    if (value == "true")
    {
      uint_val = 1;
    }
    else if (value == "false")
    {
      uint_val = 0;
    }
    else
    {
      uint_val = std::stoi(value);
    }

    bool option_set = false;
    BtorOption opt;
    for (opt = boolector_first_opt(btor.get());
         boolector_has_opt(btor.get(), opt);
         opt = boolector_next_opt(btor.get(), opt))
    {
      if (option == boolector_get_opt_lng(btor.get(), opt))
      {
        boolector_set_opt(btor.get(), opt, uint_val);
        option_set = true;
        break;
      }
    }

    if (!option_set)
    {
      std::string msg("Option ");
      msg += option;
      msg += " could not be found in the boolector backend.";
      throw NotImplementedException(msg);
    }
  }
}

void BoolectorSolver::set_logic(const std::string logic)
{
  if (supported_logics.find(logic) == supported_logics.end())
  {
    throw IncorrectUsageException(
        "Boolector only supports logics using bit-vectors, arrays and "
        "uninterpreted functions");
  }
}

Term BoolectorSolver::make_term(bool b) const
{
  if (b)
  {
    return std::make_shared<BoolectorTerm>(btor,
                                           boolector_const(btor.get(), "1"));
  }
  else
  {
    return std::make_shared<BoolectorTerm>(btor,
                                           boolector_const(btor.get(), "0"));
  }
}

Term BoolectorSolver::make_term(int64_t i, const Sort & sort) const
{
  try
  {
    std::shared_ptr<BoolectorSortBase> bs =
        std::static_pointer_cast<BoolectorSortBase>(sort);
    // note: give the constant value a null PrimOp
    if (i >= std::numeric_limits<int32_t>::min()
        && i <= std::numeric_limits<int32_t>::max())
    {
      return std::make_shared<BoolectorTerm>(
          btor, boolector_int(btor.get(), i, bs->sort));
    }
    // boolector_int takes an int32_t, so write out the bits it would give a
    // wider value: truncated to the width, or sign-extended to it
    uint64_t width = sort->get_width();
    std::string bits(width, '0');
    for (uint64_t k = 0; k < width; ++k)
    {
      bool bit = k < 64 ? (static_cast<uint64_t>(i) >> k) & 1 : i < 0;
      bits[width - 1 - k] = bit ? '1' : '0';
    }
    return std::make_shared<BoolectorTerm>(
        btor, boolector_const(btor.get(), bits.c_str()));
  }
  catch (InternalSolverException & e)
  {
    // pretty safe to assume that an error here is due to incorrect usage
    throw IncorrectUsageException(e.what());
  }
}

Term BoolectorSolver::make_term(std::string val,
                                const Sort & sort,
                                uint64_t base) const
{
  try
  {
    // Boolector's own string constructors ignore the sort in base 2, read a
    // minus differently in base 16 and accept malformed numerals, so write
    // out the bits of the value and build that
    std::string bits = bv_value_to_bits(val, base, sort);
    return std::make_shared<BoolectorTerm>(
        btor, boolector_const(btor.get(), bits.c_str()));
  }
  catch (InternalSolverException & e)
  {
    // pretty safe to assume that an error here is due to incorrect usage
    throw IncorrectUsageException(e.what());
  }
}

Term BoolectorSolver::make_term(const Term & val, const Sort & sort) const
{
  if (sort->get_sort_kind() == ARRAY)
  {
    std::shared_ptr<BoolectorTerm> bt =
        std::static_pointer_cast<BoolectorTerm>(val);
    std::shared_ptr<BoolectorSortBase> bs =
        std::static_pointer_cast<BoolectorSortBase>(sort);
    return std::make_shared<BoolectorTerm>(
        btor, boolector_const_array(btor.get(), bs->sort, bt->node));
  }
  else
  {
    throw IncorrectUsageException(
        "Constant arrays are the only value that can be created with "
        "mkTerm(Term, Sort) but the sort is not an array sort.");
  }
}

void BoolectorSolver::assert_formula(const Term & t)
{
  std::shared_ptr<BoolectorTerm> bt =
      std::static_pointer_cast<BoolectorTerm>(t);
  boolector_assert(btor.get(), bt->node);
}

Result BoolectorSolver::check_sat() { return solve(); }

Result BoolectorSolver::check_sat_assuming(const TermVec & assumptions)
{
  for (const Term & a : assumptions)
  {
    std::shared_ptr<BoolectorTerm> bt =
        std::static_pointer_cast<BoolectorTerm>(a);
    assert(boolector_get_width(bt->btor.get(), bt->node) == 1);
    boolector_assume(btor.get(), bt->node);
  }

  return solve();
}

Result BoolectorSolver::solve()
{
  if (time_limit != std::chrono::duration<double>::zero())
  {
    deadline =
        std::chrono::steady_clock::now()
        + std::chrono::duration_cast<std::chrono::steady_clock::duration>(
            time_limit);
    // Boolector latches termination and has no API to clear it, so without
    // this every query after the first timeout would answer unknown.
    btor->cbs.term.done = 0;
  }

  int32_t res = boolector_sat(btor.get());
  if (res == BOOLECTOR_SAT)
  {
    return Result(SAT);
  }
  else if (res == BOOLECTOR_UNSAT)
  {
    return Result(UNSAT);
  }
  else if (btor->cbs.term.done)
  {
    return Result(UNKNOWN, "Time limit reached.");
  }
  else
  {
    return Result(UNKNOWN);
  }
}

void BoolectorSolver::do_push(uint64_t num) { boolector_push(btor.get(), num); }

void BoolectorSolver::do_pop(uint64_t num) { boolector_pop(btor.get(), num); }

Term BoolectorSolver::get_value(const Term & t) const
{
  Term result;
  std::shared_ptr<BoolectorTerm> bt =
      std::static_pointer_cast<BoolectorTerm>(t);
  Sort sort = t->get_sort();
  SortKind sk = sort->get_sort_kind();
  if ((sk == BV) || (sk == BOOL))
  {
    const char * assignment = boolector_bv_assignment(btor.get(), bt->node);
    BoolectorNode * bc = boolector_const(btor.get(), assignment);
    boolector_free_bv_assignment(btor.get(), assignment);
    // note: give the constant value a null PrimOp
    result = std::make_shared<BoolectorTerm>(btor, bc);
  }
  else if (sk == ARRAY)
  {
    std::shared_ptr<BoolectorSortBase> bs =
        std::static_pointer_cast<BoolectorSortBase>(sort);

    std::shared_ptr<BoolectorSortBase> b_elemsort =
        std::static_pointer_cast<BoolectorSortBase>(sort->get_elemsort());

    BoolectorNode * zero = boolector_zero(btor.get(), b_elemsort->sort);
    BoolectorNode * stores = boolector_const_array(btor.get(), bs->sort, zero);
    boolector_release(btor.get(), zero);

    char ** indices;
    char ** values;
    uint32_t size;
    boolector_array_assignment(btor.get(), bt->node, &indices, &values, &size);

    // do a first pass to find constant array base
    for (uint32_t i = 0; i < size; i++)
    {
      if (std::string(indices[i]) == "*")
      {
        BoolectorNode * const_val = boolector_const(btor.get(), values[i]);
        boolector_release(btor.get(), stores);
        stores = boolector_const_array(btor.get(), bs->sort, const_val);
        boolector_release(btor.get(), const_val);
      }
    }

    BoolectorNode * idx;
    BoolectorNode * elem;
    BoolectorNode * tmp;
    for (uint32_t i = 0; i < size; i++)
    {
      if (std::string(indices[i]) == "*")
      {
        continue;
      }

      idx = boolector_const(btor.get(), indices[i]);
      elem = boolector_const(btor.get(), values[i]);

      tmp = boolector_write(btor.get(), stores, idx, elem);
      boolector_release(btor.get(), stores);
      stores = tmp;

      boolector_release(btor.get(), idx);
      boolector_release(btor.get(), elem);
    }
    result = std::make_shared<BoolectorTerm>(btor, stores);

    // free memory
    if (size)
    {
      boolector_free_array_assignment(btor.get(), indices, values, size);
    }
  }
  else if (sk == FUNCTION)
  {
    throw NotImplementedException("UF models unimplemented.");
  }
  else
  {
    std::string msg("Can't get value for term with sort constructor = ");
    msg += to_string(sk);
    throw IncorrectUsageException(msg);
  }
  return result;
}

UnorderedTermMap BoolectorSolver::get_array_values(const Term & arr,
                                                   Term & out_const_base) const
{
  Sort arrsort = arr->get_sort();
  assert(arrsort->get_sort_kind() == ARRAY);

  // assume base is zero
  // if it's not, it will be changed below
  out_const_base = make_term(0, arrsort->get_elemsort());

  UnorderedTermMap assignments;

  std::shared_ptr<BoolectorTerm> barr =
      std::static_pointer_cast<BoolectorTerm>(arr);

  char ** bindices;
  char ** bvalues;
  uint32_t size;
  boolector_array_assignment(
      btor.get(), barr->node, &bindices, &bvalues, &size);
  BoolectorNode * bidx;
  BoolectorNode * belem;
  for (uint32_t i = 0; i < size; i++)
  {
    if (std::string(bindices[i]) == "*")
    {
      belem = boolector_const(btor.get(), bvalues[i]);
      out_const_base = Term(new BoolectorTerm(btor, belem));
    }
    else
    {
      bidx = boolector_const(btor.get(), bindices[i]);
      belem = boolector_const(btor.get(), bvalues[i]);

      Term idx = Term(new BoolectorTerm(btor, bidx));
      Term val = Term(new BoolectorTerm(btor, belem));

      assignments[idx] = val;
    }
  }

  // free memory
  if (size)
  {
    boolector_free_array_assignment(btor.get(), bindices, bvalues, size);
  }

  return assignments;
}

void BoolectorSolver::get_unsat_assumptions(UnorderedTermSet & out) const
{
  BoolectorNode ** bcore = boolector_get_failed_assumptions(btor.get());
  while (*bcore)
  {
    out.insert(std::make_shared<BoolectorTerm>(
        btor, boolector_copy(btor.get(), *bcore)));
    ++bcore;
  }
}

Sort BoolectorSolver::make_sort(const std::string /* name */,
                                uint64_t /* arity */) const
{
  throw NotImplementedException("Uninterpreted sorts are not supported by "
                                + to_string(solver_enum));
}

Sort BoolectorSolver::make_sort(SortKind sk) const
{
  if (sk == BOOL)
  {
    return std::make_shared<BoolectorBVSort>(
        btor, boolector_bool_sort(btor.get()), 1);
  }
  else
  {
    std::string msg("Boolector does not support sort ");
    msg += to_string(sk);
    throw NotImplementedException(msg);
  }
}

Sort BoolectorSolver::make_sort(SortKind sk, uint64_t size) const
{
  if (sk == BV)
  {
    return std::make_shared<BoolectorBVSort>(
        btor, boolector_bitvec_sort(btor.get(), size), size);
  }
  else
  {
    std::string msg("Can't create sort from sort kind ");
    msg += to_string(sk);
    msg += " with int argument.";
    throw IncorrectUsageException(msg);
  }
}

Sort BoolectorSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  if (sk == FUNCTION)
  {
    if (sorts.size() < 2)
    {
      throw IncorrectUsageException(
          "Function sort must have >=2 sort arguments.");
    }

    Sort returnsort = sorts.back();
    std::shared_ptr<BoolectorSortBase> btor_return_sort =
        std::static_pointer_cast<BoolectorSortBase>(returnsort);

    // arity is one less, because last sort is return sort
    uint32_t arity = sorts.size() - 1;
    std::vector<BoolectorSort> btor_sorts;
    btor_sorts.reserve(arity);
    for (size_t i = 0; i < arity; i++)
    {
      std::shared_ptr<BoolectorSortBase> bs =
          std::static_pointer_cast<BoolectorSortBase>(sorts[i]);
      btor_sorts.push_back(bs->sort);
    }

    BoolectorSort btor_fun_sort = boolector_fun_sort(
        btor.get(), btor_sorts.data(), arity, btor_return_sort->sort);
    SortVec domain_sorts(sorts.begin(), sorts.end() - 1);
    return std::make_shared<BoolectorUFSort>(
        btor, btor_fun_sort, domain_sorts, returnsort);
  }
  else if (sk == ARRAY && sorts.size() == 2)
  {
    std::shared_ptr<BoolectorSortBase> btor_idxsort =
        std::static_pointer_cast<BoolectorSortBase>(sorts[0]);
    std::shared_ptr<BoolectorSortBase> btor_elemsort =
        std::static_pointer_cast<BoolectorSortBase>(sorts[1]);
    BoolectorSort bs = boolector_array_sort(
        btor.get(), btor_idxsort->sort, btor_elemsort->sort);
    return std::make_shared<BoolectorArraySort>(btor, bs, sorts[0], sorts[1]);
  }
  else
  {
    std::string msg("Can't create sort from sort constructor ");
    msg += to_string(sk);
    msg += " with a vector of sorts of size " + std::to_string(sorts.size());
    throw IncorrectUsageException(msg);
  }
}

Term BoolectorSolver::make_symbol(const std::string name, const Sort & sort)
{
  // check that name is available
  // avoids memory leak when boolector aborts
  if (symbol_table.find(name) != symbol_table.end())
  {
    throw IncorrectUsageException("symbol " + name + " has already been used.");
  }

  std::shared_ptr<BoolectorSortBase> bs =
      std::static_pointer_cast<BoolectorSortBase>(sort);

  SortKind sk = sort->get_sort_kind();
  BoolectorNode * n;
  if (sk == ARRAY)
  {
    n = boolector_array(btor.get(), bs->sort, name.c_str());
  }
  else if (sk == FUNCTION)
  {
    n = boolector_uf(btor.get(), bs->sort, name.c_str());
  }
  else
  {
    n = boolector_var(btor.get(), bs->sort, name.c_str());
  }

  // note: giving the symbol a null Op
  Term term = std::make_shared<BoolectorTerm>(btor, n);
  symbol_table[name] = term;
  return term;
}

Term BoolectorSolver::get_symbol(const std::string & name) const
{
  auto it = symbol_table.find(name);
  if (it == symbol_table.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist.");
  }
  return it->second;
}

Term BoolectorSolver::make_param(const std::string /* name */,
                                 const Sort & sort) const
{
  std::shared_ptr<BoolectorSortBase> bs =
      std::static_pointer_cast<BoolectorSortBase>(sort);
  // The name goes unused: Boolector keeps one table of names for params and
  // variables, so a named param would refuse a symbol of its name, or be
  // refused by one
  BoolectorNode * n = boolector_param(btor.get(), bs->sort, nullptr);
  return std::make_shared<BoolectorTerm>(btor, n);
}

Term BoolectorSolver::make_term(Op op, const TermVec & terms) const
{
  size_t size = terms.size();
  if (!size)
  {
    throw IncorrectUsageException("Can't apply " + op.to_string()
                                  + " to zero terms.");
  }
  else if (op.prim_op == Forall || op.prim_op == Exists)
  {
    check_quantifier_binders(op, terms);
  }

  std::vector<BoolectorNode *> nodes;
  nodes.reserve(size);
  for (const auto & t : terms)
  {
    nodes.push_back(std::static_pointer_cast<BoolectorTerm>(t)->node);
  }

  BoolectorNode * btor_res;
  if (size == 1)
  {
    if (op.prim_op == Extract)
    {
      btor_res = boolector_slice(btor.get(),
                                 nodes[0],
                                 narrow_index(op, op.idx0),
                                 narrow_index(op, op.idx1));
    }
    else if (op.prim_op == Zero_Extend)
    {
      btor_res =
          boolector_uext(btor.get(), nodes[0], narrow_index(op, op.idx0));
    }
    else if (op.prim_op == Sign_Extend)
    {
      btor_res =
          boolector_sext(btor.get(), nodes[0], narrow_index(op, op.idx0));
    }
    else if (op.prim_op == Repeat)
    {
      if (op.idx0 < 1)
      {
        throw IncorrectUsageException("Can't create repeat with index < 1");
      }
      btor_res =
          boolector_repeat(btor.get(), nodes[0], narrow_index(op, op.idx0));
    }
    else if (op.prim_op == Rotate_Left)
    {
      btor_res = custom_boolector_rotate_left(
          btor.get(), nodes[0], narrow_index(op, op.idx0));
    }
    else if (op.prim_op == Rotate_Right)
    {
      btor_res = custom_boolector_rotate_right(
          btor.get(), nodes[0], narrow_index(op, op.idx0));
    }
    else if (!op.num_idx)
    {
      auto it = unary_ops.find(op.prim_op);
      if (it == unary_ops.end())
      {
        throw IncorrectUsageException(
            to_string(op.prim_op)
            + " unsupported or can't be applied to a single term.");
      }
      btor_res = it->second(btor.get(), nodes[0]);
    }
    else
    {
      std::string msg = "Could not find Boolector implementation of ";
      msg += to_string(op.prim_op);
      throw IncorrectUsageException(msg);
    }
  }
  else if (op.num_idx)
  {
    throw IncorrectUsageException(
        "There are no supported indexed operators that take more than one "
        "argument");
  }
  else if (op.prim_op == Apply)
  {
    // the first term is the function, applied to the rest
    btor_res =
        boolector_apply(btor.get(), nodes.data() + 1, size - 1, nodes[0]);
  }
  else if (op.prim_op == Forall || op.prim_op == Exists)
  {
    // the last term is the body, bound by the rest
    btor_res =
        op.prim_op == Forall
            ? boolector_forall(btor.get(), nodes.data(), size - 1, nodes.back())
            : boolector_exists(
                  btor.get(), nodes.data(), size - 1, nodes.back());
  }
  else if (size == 2 && binary_ops.find(op.prim_op) != binary_ops.end())
  {
    btor_res = binary_ops.at(op.prim_op)(btor.get(), nodes[0], nodes[1]);
  }
  else if (size == 3 && ternary_ops.find(op.prim_op) != ternary_ops.end())
  {
    btor_res =
        ternary_ops.at(op.prim_op)(btor.get(), nodes[0], nodes[1], nodes[2]);
  }
  else if (size == 2)
  {
    throw IncorrectUsageException(
        to_string(op.prim_op)
        + " unsupported or can't be applied to two terms.");
  }
  else
  {
    return make_nary_term(this, op, terms);
  }

  return std::make_shared<BoolectorTerm>(btor, btor_res);
}

void BoolectorSolver::do_reset()
{
  // forget the symbols, so that their names can be declared again; terms
  // still held from before keep the old instance alive
  symbol_table.clear();
  // a handle from get_btor() keeps the old instance, which then runs
  // without this solver's time limit
  boolector_set_term(btor.get(), nullptr, nullptr);
  btor = new_btor();
  boolector_set_term(btor.get(), reached_deadline, this);
  // the new instance starts at context 0 with default options, so the
  // bookkeeping for the old one goes too
  base_context_1 = false;
  time_limit = std::chrono::duration<double>::zero();
}

void BoolectorSolver::do_reset_assertions()
{
  if (!base_context_1)
  {
    throw NotImplementedException(
        "Boolector does not support reset_assertions. "
        "However, you can use set_opt(\"base-context-1\", \"true\")"
        " to do all solving at context 1, which then will allow "
        " calling reset_assertions. This may impact performance");
  }
  else
  {
    // pop the contexts, and the hidden base context under them
    boolector_pop(btor.get(), get_context_level() + 1);
    // push the base context back
    boolector_push(btor.get(), 1);
  }
}

Term BoolectorSolver::substitute(
    const Term term, const UnorderedTermMap & substitution_map) const
{
  BoolectorNodeMap * bmap = boolector_nodemap_new(btor.get());

  std::shared_ptr<BoolectorTerm> bt =
      std::static_pointer_cast<BoolectorTerm>(term);

  std::shared_ptr<BoolectorTerm> key;
  std::shared_ptr<BoolectorTerm> value;
  for (auto elem : substitution_map)
  {
    key = std::static_pointer_cast<BoolectorTerm>(elem.first);
    value = std::static_pointer_cast<BoolectorTerm>(elem.second);
    // boolectornodemap only supports var -> term mappings
    if (!key->is_symbol())
    {
      throw IncorrectUsageException(
          "boolector backend currently only supports symbol->term "
          "substitution");
    }
    boolector_nodemap_map(bmap, key->node, value->node);
  }

  // perform the substitution
  BoolectorNode * substituted =
      boolector_nodemap_substitute_node(btor.get(), bmap, bt->node);
  // need to copy it because deleting the map will decrement the reference
  // counter
  substituted = boolector_copy(btor.get(), substituted);
  boolector_nodemap_delete(bmap);
  return std::make_shared<BoolectorTerm>(btor, substituted);
}

void BoolectorSolver::dump_smt2(std::string filename) const
{
  FILE * file = fopen(filename.c_str(), "w");
  boolector_dump_smt2(btor.get(), file);
  fclose(file);
}

/* end BoolectorSolver implementation */

}  // namespace smt
