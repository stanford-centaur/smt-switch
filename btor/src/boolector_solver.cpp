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

// Indexed Operators are implemented in boolector_solver.h in apply
const std::unordered_map<PrimOp, bin_fun> binary_ops(
    { { And, boolector_and },
      { Or, boolector_or },
      { Xor, boolector_xor },
      { Implies, boolector_implies },
      { Iff, boolector_iff },
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

void BoolectorSolver::set_opt(const std::string option, const std::string value)
{
  if (option == "produce-models")
  {
    if (value == "true")
    {
      boolector_set_opt(btor, BTOR_OPT_MODEL_GEN, 1);
    }
  }
  else if (option == "incremental")
  {
    if (value == "true")
    {
      boolector_set_opt(btor, BTOR_OPT_INCREMENTAL, 1);
    }
  }
  else if (option == "produce-unsat-cores")
  {
    if (value == "true")
    {
      // needs to be incremental
      boolector_set_opt(btor, BTOR_OPT_INCREMENTAL, 1);
    }
  }
  else if (option == "base-context-1" && value == "true")
  {
    base_context_1 = true;
    push(1);
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
    for (opt = boolector_first_opt(btor); boolector_has_opt(btor, opt);
         opt = boolector_next_opt(btor, opt))
    {
      if (option == boolector_get_opt_lng(btor, opt))
      {
        boolector_set_opt(btor, opt, uint_val);
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


Sort BoolectorSolver::make_sort(const DatatypeDecl & d) const {
  throw NotImplementedException("BoolectorSolver::make_sort");
};
DatatypeDecl BoolectorSolver::make_datatype_decl(const std::string & s)  {
    throw NotImplementedException("BoolectorSolver::make_datatype_decl");
}
DatatypeConstructorDecl BoolectorSolver::make_datatype_constructor_decl(
    const std::string s)
{
  throw NotImplementedException(
      "BoolectorSolver::make_datatype_constructor_decl");
};
void BoolectorSolver::add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const {
  throw NotImplementedException("BoolectorSolver::add_constructor");
};
void BoolectorSolver::add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const {
  throw NotImplementedException("BoolectorSolver::add_selector");
};
void BoolectorSolver::add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const {
  throw NotImplementedException("BoolectorSolver::add_selector_self");
};

Term BoolectorSolver::get_constructor(const Sort & s, std::string name) const  {
  throw NotImplementedException("BoolectorSolver::get_constructor");
};
Term BoolectorSolver::get_tester(const Sort & s, std::string name) const  {
  throw NotImplementedException("BoolectorSolver::get_testeer");
};

Term BoolectorSolver::get_selector(const Sort & s, std::string con, std::string name) const  {
  throw NotImplementedException("BoolectorSolver::get_selector");
};


Term BoolectorSolver::make_term(bool b) const
{
  if (b)
  {
    return std::make_shared<BoolectorTerm> (btor, boolector_const(btor, "1"));
  }
  else
  {
    return std::make_shared<BoolectorTerm> (btor, boolector_const(btor, "0"));
  }
}

Term BoolectorSolver::make_term(int64_t i, const Sort & sort) const
{
  try
  {
    std::shared_ptr<BoolectorSortBase> bs =
        std::static_pointer_cast<BoolectorSortBase>(sort);
    // note: give the constant value a null PrimOp
    return std::make_shared<BoolectorTerm> (btor, boolector_int(btor, i, bs->sort));
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
    std::shared_ptr<BoolectorSortBase> bs =
        std::static_pointer_cast<BoolectorSortBase>(sort);

    BoolectorNode * node;
    if (base == 10)
    {
      node = boolector_constd(btor, bs->sort, val.c_str());
    }
    else if (base == 2)
    {
      node = boolector_const(btor, val.c_str());
    }
    else if (base == 16)
    {
      node = boolector_consth(btor, bs->sort, val.c_str());
    }
    else
    {
      throw IncorrectUsageException(
          "Only accepted bases are 2, 10 and 16, but got "
          + std::to_string(base));
    }

    return std::make_shared<BoolectorTerm> (btor, node);
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
    return std::make_shared<BoolectorTerm>
        (btor, boolector_const_array(btor, bs->sort, bt->node));
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
  boolector_assert(btor, bt->node);
}

Result BoolectorSolver::check_sat()
{
  int32_t res = boolector_sat(btor);
  if (res == BOOLECTOR_SAT)
  {
    return Result(SAT);
  }
  else if (res == BOOLECTOR_UNSAT)
  {
    return Result(UNSAT);
  }
  else
  {
    return Result(UNKNOWN);
  }
};

Result BoolectorSolver::check_sat_assuming(const TermVec & assumptions)
{
  // boolector supports assuming arbitrary one-bit expressions,
  // not just boolean literals
  std::shared_ptr<BoolectorTerm> bt;
  for (auto a : assumptions)
  {
    bt = std::static_pointer_cast<BoolectorTerm>(a);

    bool is_literal = true;

    BoolectorSort s = boolector_get_sort(bt->btor, bt->node);
    // booleans are bit-vectors in boolector
    is_literal &= boolector_is_bitvec_sort(bt->btor, s);
    is_literal &= boolector_get_width(bt->btor, bt->node) == 1;

    bool const_or_negated = a->is_symbolic_const();
    if (!const_or_negated && bt->negated)
    {
      Term c = *(a->begin());
      const_or_negated = c->is_symbolic_const();
    }
    is_literal &= const_or_negated;

    if (!is_literal)
    {
      throw IncorrectUsageException(
          "Assumptions to check_sat_assuming must be boolean literals");
    }

    boolector_assume(btor, bt->node);
  }

  int32_t res = boolector_sat(btor);
  if (res == BOOLECTOR_SAT)
  {
    return Result(SAT);
  }
  else if (res == BOOLECTOR_UNSAT)
  {
    return Result(UNSAT);
  }
  else
  {
    return Result(UNKNOWN);
  }
}

void BoolectorSolver::push(uint64_t num)
{
  boolector_push(btor, num);
  context_level += num;
}

void BoolectorSolver::pop(uint64_t num)
{
  boolector_pop(btor, num);
  context_level -= num;
}

Term BoolectorSolver::get_value(const Term & t) const
{
  Term result;
  std::shared_ptr<BoolectorTerm> bt =
      std::static_pointer_cast<BoolectorTerm>(t);
  Sort sort = t->get_sort();
  SortKind sk = sort->get_sort_kind();
  if ((sk == BV) || (sk == BOOL))
  {
    const char * assignment = boolector_bv_assignment(btor, bt->node);
    BoolectorNode * bc = boolector_const(btor, assignment);
    boolector_free_bv_assignment(btor, assignment);
    // note: give the constant value a null PrimOp
    result = std::make_shared<BoolectorTerm>(btor, bc);
  }
  else if (sk == ARRAY)
  {
    std::shared_ptr<BoolectorSortBase> bs =
        std::static_pointer_cast<BoolectorSortBase>(sort);

    std::shared_ptr<BoolectorSortBase> b_elemsort =
        std::static_pointer_cast<BoolectorSortBase>(sort->get_elemsort());

    BoolectorNode * zero = boolector_zero(btor, b_elemsort->sort);
    BoolectorNode * stores = boolector_const_array(btor, bs->sort, zero);
    boolector_release(btor, zero);

    char ** indices;
    char ** values;
    uint32_t size;
    boolector_array_assignment(btor, bt->node, &indices, &values, &size);

    // do a first pass to find constant array base
    for (uint32_t i = 0; i < size; i++)
    {
      if (std::string(indices[i]) == "*")
      {
        BoolectorNode * const_val = boolector_const(btor, values[i]);
        boolector_release(btor, stores);
        stores = boolector_const_array(btor, bs->sort, const_val);
        boolector_release(btor, const_val);
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

      idx = boolector_const(btor, indices[i]);
      elem = boolector_const(btor, values[i]);

      tmp = boolector_write(btor, stores, idx, elem);
      boolector_release(btor, stores);
      stores = tmp;

      boolector_release(btor, idx);
      boolector_release(btor, elem);
    }
    result = std::make_shared<BoolectorTerm>(btor, stores);

    // free memory
    if (size)
    {
      boolector_free_array_assignment(btor, indices, values, size);
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
    throw IncorrectUsageException(msg.c_str());
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
  boolector_array_assignment(btor, barr->node, &bindices, &bvalues, &size);
  BoolectorNode * bidx;
  BoolectorNode * belem;
  Term idx;
  Term val;
  for (uint32_t i = 0; i < size; i++)
  {
    if (std::string(bindices[i]) == "*")
    {
      belem = boolector_const(btor, bvalues[i]);
      out_const_base = Term(new BoolectorTerm(btor, belem));
    }
    else
    {
      bidx = boolector_const(btor, bindices[i]);
      belem = boolector_const(btor, bvalues[i]);

      Term idx = Term(new BoolectorTerm(btor, bidx));
      Term val = Term(new BoolectorTerm(btor, belem));

      assignments[idx] = val;
    }
  }

  // free memory
  if (size)
  {
    boolector_free_array_assignment(btor, bindices, bvalues, size);
  }

  return assignments;
}

void BoolectorSolver::get_unsat_core(UnorderedTermSet & out)
{
  BoolectorNode ** bcore = boolector_get_failed_assumptions(btor);
  while (*bcore)
  {
    out.insert(std::make_shared<BoolectorTerm>(
        btor, boolector_copy(btor, *bcore)));
    ++bcore;
  }
}

Sort BoolectorSolver::make_sort(const std::string name, uint64_t arity) const
{
  throw IncorrectUsageException("Can't declare sorts with Boolector");
}

Sort BoolectorSolver::make_sort(SortKind sk) const
{
  if (sk == BOOL)
  {
    return std::make_shared<BoolectorBVSort>
        (btor, boolector_bool_sort(btor), 1);
  }
  else
  {
    std::string msg("Boolector does not support sort ");
    msg += to_string(sk);
    throw NotImplementedException(msg.c_str());
  }
}

Sort BoolectorSolver::make_sort(SortKind sk, uint64_t size) const
{
  if (sk == BV)
  {
    return std::make_shared<BoolectorBVSort>
        (btor, boolector_bitvec_sort(btor, size), size);
  }
  else
  {
    std::string msg("Can't create sort from sort constructor ");
    msg += to_string(sk);
    msg += " with int argument.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort BoolectorSolver::make_sort(SortKind sk, const Sort & sort1) const
{
  throw IncorrectUsageException(
      "Boolector has no sort that takes a single sort argument.");
}

Sort BoolectorSolver::make_sort(SortKind sk,
                                const Sort & sort1,
                                const Sort & sort2) const
{
  if (sk == ARRAY)
  {
    std::shared_ptr<BoolectorSortBase> btor_idxsort =
        std::static_pointer_cast<BoolectorSortBase>(sort1);
    std::shared_ptr<BoolectorSortBase> btor_elemsort =
        std::static_pointer_cast<BoolectorSortBase>(sort2);
    BoolectorSort bs =
        boolector_array_sort(btor, btor_idxsort->sort, btor_elemsort->sort);
    return std::make_shared<BoolectorArraySort> (btor, bs, sort1, sort2);
  }
  else
  {
    std::string msg("Can't create sort from sort constructor ");
    msg += to_string(sk);
    msg += " with two sort arguments.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort BoolectorSolver::make_sort(SortKind sk,
                                const Sort & sort1,
                                const Sort & sort2,
                                const Sort & sort3) const
{
  throw IncorrectUsageException(
      "Boolector does not have a non-function sort that takes three sort "
      "arguments");
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

    BoolectorSort btor_fun_sort =
        boolector_fun_sort(btor, &btor_sorts[0], arity, btor_return_sort->sort);
    return std::make_shared<BoolectorUFSort>
        (btor, btor_fun_sort, sorts, returnsort);
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
    throw IncorrectUsageException(msg.c_str());
  }
}

Sort BoolectorSolver::make_sort(const Sort & sort_con,
                                const SortVec & sorts) const

{
  throw IncorrectUsageException(
      "Boolector does not support uninterpreted sort construction");
}

Term BoolectorSolver::make_symbol(const std::string name, const Sort & sort)
{
  // check that name is available
  // avoids memory leak when boolector aborts
  if (symbol_names.find(name) != symbol_names.end())
  {
    throw IncorrectUsageException("symbol " + name + " has already been used.");
  }

  std::shared_ptr<BoolectorSortBase> bs =
      std::static_pointer_cast<BoolectorSortBase>(sort);

  SortKind sk = sort->get_sort_kind();
  BoolectorNode * n;
  if (sk == ARRAY)
  {
    n = boolector_array(btor, bs->sort, name.c_str());
  }
  else if (sk == FUNCTION)
  {
    n = boolector_uf(btor, bs->sort, name.c_str());
  }
  else
  {
    n = boolector_var(btor, bs->sort, name.c_str());
  }

  // note: giving the symbol a null Op
  Term term = std::make_shared<BoolectorTerm> (btor, n);
  symbol_names.insert(name);
  return term;
}

Term BoolectorSolver::make_param(const std::string name, const Sort & sort)
{
  std::shared_ptr<BoolectorSortBase> bs =
      std::static_pointer_cast<BoolectorSortBase>(sort);
  BoolectorNode * n = boolector_param(btor, bs->sort, name.c_str());
  return std::make_shared<BoolectorTerm>(btor, n);
}

Term BoolectorSolver::make_term(Op op, const Term & t) const
{
  if (op.prim_op == Forall || op.prim_op == Exists)
  {
    throw IncorrectUsageException(
        "Expecting exactly one parameter and a body formula for quantifier op");
  }
  if (op.num_idx == 0)
  {
    return apply_prim_op(op.prim_op, t);
  }
  else
  {
    std::shared_ptr<BoolectorTerm> bt =
        std::static_pointer_cast<BoolectorTerm>(t);
    BoolectorNode * btor_res;
    if (op.prim_op == Extract)
    {
      btor_res = boolector_slice(btor, bt->node, op.idx0, op.idx1);
    }
    else if (op.prim_op == Zero_Extend)
    {
      btor_res = boolector_uext(btor, bt->node, op.idx0);
    }
    else if (op.prim_op == Sign_Extend)
    {
      btor_res = boolector_sext(btor, bt->node, op.idx0);
    }
    else if (op.prim_op == Repeat)
    {
      btor_res = boolector_repeat(btor, bt->node, op.idx0);
    }
    else if (op.prim_op == Rotate_Left)
    {
      btor_res = custom_boolector_rotate_left(btor, bt->node, op.idx0);
    }
    else if (op.prim_op == Rotate_Right)
    {
      btor_res = custom_boolector_rotate_right(btor, bt->node, op.idx0);
    }
    else
    {
      std::string msg = "Could not find Boolector implementation of ";
      msg += to_string(op.prim_op);
      throw IncorrectUsageException(msg.c_str());
    }
    return std::make_shared<BoolectorTerm> (btor, btor_res);
  }
}

Term BoolectorSolver::make_term(Op op, const Term & t0, const Term & t1) const
{
  if (op.num_idx == 0)
  {
    return apply_prim_op(op.prim_op, t0, t1);
  }
  else
  {
    throw IncorrectUsageException(
        "There are no supported indexed operators that take more than one "
        "argument");
  }
}

Term BoolectorSolver::make_term(Op op,
                                const Term & t0,
                                const Term & t1,
                                const Term & t2) const
{
  if (op.prim_op == Forall || op.prim_op == Exists)
  {
    throw IncorrectUsageException(
        "Expecting exactly one parameter and a body formula for quantifier op");
  }
  else if (op.num_idx == 0)
  {
    return apply_prim_op(op.prim_op, t0, t1, t2);
  }
  else
  {
    throw IncorrectUsageException(
        "There are no supported indexed operators that take more than one "
        "argument");
  }
}

Term BoolectorSolver::make_term(Op op, const TermVec & terms) const
{
  if (terms.size() != 2 && (op.prim_op == Forall || op.prim_op == Exists))
  {
    throw IncorrectUsageException(
        "Expecting exactly one parameter and a body formula for quantifier op");
  }
  else if (op.num_idx == 0)
  {
    return apply_prim_op(op.prim_op, terms);
  }
  else
  {
    if (terms.size() == 1)
    {
      return make_term(op, terms[0]);
    }
    else
    {
      throw IncorrectUsageException(
          "There are no supported indexed operators that take more than one "
          "argument");
    }
  }
}

void BoolectorSolver::reset()
{
  boolector_release_all(btor);
  boolector_delete(btor);
  btor = boolector_new();
}

void BoolectorSolver::reset_assertions()
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
    // pop the contexts
    pop(context_level);
    // push back to context level 1
    push(1);
    assert(context_level == 1);
  }
}

Term BoolectorSolver::substitute(
    const Term term, const UnorderedTermMap & substitution_map) const
{
  BoolectorNodeMap * bmap = boolector_nodemap_new(btor);

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
      boolector_nodemap_substitute_node(btor, bmap, bt->node);
  // need to copy it because deleting the map will decrement the reference
  // counter
  substituted = boolector_copy(btor, substituted);
  boolector_nodemap_delete(bmap);
  return std::make_shared<BoolectorTerm> (btor, substituted);
}

void BoolectorSolver::dump_smt2(std::string filename) const
{
  FILE * file = fopen(filename.c_str(), "w");
  boolector_dump_smt2(btor, file);
  fclose(file);
}

Term BoolectorSolver::apply_prim_op(PrimOp op, Term t) const
{
  try
  {
    std::shared_ptr<BoolectorTerm> bt =
        std::static_pointer_cast<BoolectorTerm>(t);
    BoolectorNode * result = unary_ops.at(op)(btor, bt->node);
    return std::make_shared<BoolectorTerm> (btor, result);
  }
  catch (std::out_of_range & o)
  {
    std::string msg(to_string(op));
    msg += " unsupported or can't be applied to a single term.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Term BoolectorSolver::apply_prim_op(PrimOp op, Term t0, Term t1) const
{
  try
  {
    std::shared_ptr<BoolectorTerm> bt0 =
        std::static_pointer_cast<BoolectorTerm>(t0);
    std::shared_ptr<BoolectorTerm> bt1 =
        std::static_pointer_cast<BoolectorTerm>(t1);

    BoolectorNode * result;
    if (op == Apply)
    {
      std::shared_ptr<BoolectorTerm> bt =
          std::static_pointer_cast<BoolectorTerm>(t1);
      std::vector<BoolectorNode *> args = { bt->node };

      std::shared_ptr<BoolectorTerm> bt0 =
          std::static_pointer_cast<BoolectorTerm>(t0);
      result = boolector_apply(btor, &args[0], 1, bt0->node);
    }
    else if (op == Forall)
    {
      std::shared_ptr<BoolectorTerm> bt0 =
          std::static_pointer_cast<BoolectorTerm>(t0);
      std::shared_ptr<BoolectorTerm> bt1 =
          std::static_pointer_cast<BoolectorTerm>(t1);
      std::vector<BoolectorNode *> params({ bt0->node });
      return std::make_shared<BoolectorTerm>(
          btor, boolector_forall(btor, &params[0], 1, bt1->node));
    }
    else if (op == Exists)
    {
      std::shared_ptr<BoolectorTerm> bt0 =
          std::static_pointer_cast<BoolectorTerm>(t0);
      std::shared_ptr<BoolectorTerm> bt1 =
          std::static_pointer_cast<BoolectorTerm>(t1);
      std::vector<BoolectorNode *> params({ bt0->node });
      return std::make_shared<BoolectorTerm>(
          btor, boolector_exists(btor, &params[0], 1, bt1->node));
    }
    else
    {
      result = binary_ops.at(op)(btor, bt0->node, bt1->node);
    }
    return std::make_shared<BoolectorTerm> (btor, result);
  }
  catch (std::out_of_range & o)
  {
    std::string msg(to_string(op));
    msg += " unsupported or can't be applied to two terms.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Term BoolectorSolver::apply_prim_op(PrimOp op, Term t0, Term t1, Term t2) const
{
  try
  {
    std::shared_ptr<BoolectorTerm> bt0 =
        std::static_pointer_cast<BoolectorTerm>(t0);
    std::shared_ptr<BoolectorTerm> bt1 =
        std::static_pointer_cast<BoolectorTerm>(t1);
    std::shared_ptr<BoolectorTerm> bt2 =
        std::static_pointer_cast<BoolectorTerm>(t2);
    BoolectorNode * result;
    if (op == Apply)
    {
      std::shared_ptr<BoolectorTerm> bt1 =
          std::static_pointer_cast<BoolectorTerm>(t1);
      std::shared_ptr<BoolectorTerm> bt2 =
          std::static_pointer_cast<BoolectorTerm>(t2);
      std::vector<BoolectorNode *> args = { bt1->node, bt2->node };

      std::shared_ptr<BoolectorTerm> bt0 =
          std::static_pointer_cast<BoolectorTerm>(t0);
      result = boolector_apply(btor, &args[0], 2, bt0->node);
    }
    else
    {
      result = ternary_ops.at(op)(btor, bt0->node, bt1->node, bt2->node);
    }

    return std::make_shared<BoolectorTerm> (btor, result);
  }
  catch (std::out_of_range & o)
  {
    std::string msg(to_string(op));
    msg += " unsupported or can't be applied to three terms.";
    throw IncorrectUsageException(msg.c_str());
  }
}

Term BoolectorSolver::apply_prim_op(PrimOp op, TermVec terms) const
{
  uint32_t size = terms.size();
  // binary ops are most common, check this first
  if (size == 2)
  {
    return apply_prim_op(op, terms[0], terms[1]);
  }
  else if (size == 1)
  {
    return apply_prim_op(op, terms[0]);
  }
  else if (size == 3)
  {
    return apply_prim_op(op, terms[0], terms[1], terms[2]);
  }
  else
  {
    if (op == Apply)
    {
      TermVec termargs;
      termargs.reserve(size - 1);
      std::vector<BoolectorNode *> args;
      args.reserve(size - 1);
      std::shared_ptr<BoolectorTerm> bt;
      for (size_t i = 1; i < size; ++i)
      {
        bt = std::static_pointer_cast<BoolectorTerm>(terms[i]);
        args.push_back(bt->node);
        termargs.push_back(terms[i]);
      }
      std::shared_ptr<BoolectorTerm> bt0 =
          std::static_pointer_cast<BoolectorTerm>(terms[0]);
      BoolectorNode * result = boolector_apply(btor, &args[0], args.size(), bt0->node);

      return std::make_shared<BoolectorTerm> (btor, result);
    }
    else
    {
      std::string msg(to_string(op));
      msg += " cannot be applied to ";
      msg += std::to_string(size);
      msg += " terms.";
      throw IncorrectUsageException(msg.c_str());
    }
  }
}

/* end BoolectorSolver implementation */

}  // namespace smt
