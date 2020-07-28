/*********************                                                        */
/*! \file boolector_term.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Boolector implementation of AbsTerm
**
**
**/

#include "boolector_term.h"

// include standard version of open_memstream
// for compatability with FreeBSD / Darwin which doesn't support it natively
extern "C"
{
#include "memstream.h"
}

#include "assert.h"
#include <unordered_map>
#include "stdio.h"

// defining hash for old compilers
namespace std
{
  // specializing template
  template<>
  struct hash<BtorNodeKind>
  {
    size_t operator()(const BtorNodeKind k) const
    {
      return static_cast<size_t>(k);
    }
  };
}

namespace smt {

/* global variables */
const std::unordered_map<BtorNodeKind, PrimOp> btorkind2primop({
    //{BTOR_INVALID_NODE}, // this should never happen
    { BTOR_BV_CONST_NODE, NUM_OPS_AND_NULL },
    { BTOR_VAR_NODE, NUM_OPS_AND_NULL },
    { BTOR_PARAM_NODE, NUM_OPS_AND_NULL },
    { BTOR_BV_SLICE_NODE, Extract },
    { BTOR_BV_AND_NODE, BVAnd },
    // note: could also use BVComp because they're indistinguishable
    // in Boolector, but expect Equal is more common
    { BTOR_BV_EQ_NODE, Equal },
    { BTOR_FUN_EQ_NODE, Equal },
    { BTOR_BV_ADD_NODE, BVAdd },
    { BTOR_BV_MUL_NODE, BVMul },
    { BTOR_BV_ULT_NODE, BVUlt },
    { BTOR_BV_SLL_NODE, BVShl },
    { BTOR_BV_SRL_NODE, BVLshr },
    { BTOR_BV_UDIV_NODE, BVUdiv },
    { BTOR_BV_UREM_NODE, BVUrem },
    { BTOR_BV_CONCAT_NODE, Concat },
    { BTOR_APPLY_NODE, Apply },
    { BTOR_FORALL_NODE, Forall },
    { BTOR_EXISTS_NODE, Exists },
    // {BTOR_LAMBDA_NODE}, // TODO: figure out when/how to use this, hopefully
    // only for quantifiers
    { BTOR_COND_NODE, Ite },
    // {BTOR_ARGS_NODE}, // should already be flattened in BoolectorTerm
    // constructor
    { BTOR_UF_NODE, NUM_OPS_AND_NULL },
    { BTOR_UPDATE_NODE, Store },
    // {BTOR_PROXY_NODE, NUM_OPS_AND_NULL} // should never happen
    // {BTOR_NUM_OPS_NOE} // should never be used
});

// helpers
Op lookup_op(Btor * btor, BoolectorNode * n)
{
  Op op;

  BtorNode * bn = BTOR_IMPORT_BOOLECTOR_NODE(n);
  if (btor_node_is_proxy(bn))
  {
    bn = btor_node_real_addr(btor_node_get_simplified(btor, bn));
  }
  BtorNodeKind k = bn->kind;

  // handle special cases
  if ((k == BTOR_APPLY_NODE) && btor_node_real_addr(bn->e[0])->is_array)
  {
    op = Op(Select);
  }
  else if (k == BTOR_BV_SLICE_NODE)
  {
    uint32_t upper = ((BtorBVSliceNode *)btor_node_real_addr(bn))->upper;
    uint32_t lower = ((BtorBVSliceNode *)btor_node_real_addr(bn))->lower;
    op = Op(Extract, upper, lower);
  }
  else if ((k == BTOR_LAMBDA_NODE) && (bn->is_array))
  {
    // constant array is a value -- give it a null operator
    op = Op();
  }
  else
  {
    if (btorkind2primop.find(k) == btorkind2primop.end())
    {
      throw SmtException("Can't find PrimOp for BtorNodeKind "
                         + std::to_string(k) + " see boolector/btornode.h");
    }
    PrimOp po = btorkind2primop.at(k);
    op = Op(po);
  }
  return op;
}

/* BoolectorTermIter implementation */

BoolectorTermIter & BoolectorTermIter::operator=(const BoolectorTermIter & it)
{
  btor = it.btor;
  children = it.children;
  idx = it.idx;
  return *this;
};

void BoolectorTermIter::operator++() { idx++; };

const Term BoolectorTermIter::operator*()
{
  assert(idx < children.size());
  BtorNode * res = children[idx];
  if (btor_node_real_addr(res)->kind == BTOR_ARGS_NODE)
  {
    throw SmtException("Should never have an args node in children look up");
  }

  // increment internal reference counter
  res = btor_node_copy(btor, res);
  // increment external reference counter
  btor_node_inc_ext_ref_counter(btor, res);

  BoolectorNode * node = BTOR_EXPORT_BOOLECTOR_NODE(res);
  return std::make_shared<BoolectorTerm> (btor, node);
};

TermIterBase * BoolectorTermIter::clone() const
{
  return new BoolectorTermIter(btor, children, idx);
}

bool BoolectorTermIter::operator==(const BoolectorTermIter & it)
{
  return ((btor == it.btor) && (idx == it.idx) && (children == it.children));
};

bool BoolectorTermIter::operator!=(const BoolectorTermIter & it)
{
  return !(*this == it);
};

bool BoolectorTermIter::equal(const TermIterBase & other) const
{
  const BoolectorTermIter & bti = static_cast<const BoolectorTermIter &>(other);
  return (*this == bti);
}

/* end BoolectorTermIter implementation */

/* BoolectorTerm implementation */

BoolectorTerm::BoolectorTerm(Btor * b, BoolectorNode * n)
    : btor(b),
      node(n),
      bn(btor_node_real_addr(BTOR_IMPORT_BOOLECTOR_NODE(n)))
{
  // BTOR_PARAM_NODE is not a symbol
  //  because it's not a symbolic constant, it's a free variable
  //  which will be bound by a lambda
  if (btor_node_is_proxy(bn))
  {
    // change to this on smtcomp19 branch -- will be merged to master soon
    // bn = btor_node_real_addr(btor_node_get_simplified(btor, bn));
    bn = btor_node_real_addr(btor_node_get_simplified(btor, bn));
  }
  negated = (((((uintptr_t)node) % 2) != 0) && bn->kind != BTOR_BV_CONST_NODE);
}

BoolectorTerm::~BoolectorTerm()
{
  boolector_release(btor, node);
}

// TODO: check if this is okay -- probably not
std::size_t BoolectorTerm::hash() const { return (std::size_t)node; };

bool BoolectorTerm::compare(const Term & absterm) const
{
  std::shared_ptr<BoolectorTerm> other =
      std::static_pointer_cast<BoolectorTerm>(absterm);
  return this->node == other->node;
}

Op BoolectorTerm::get_op() const
{
  Op op;

  if (negated)
  {
    op = Op(BVNot);
  }
  else
  {
    op = lookup_op(btor, node);
  }

  return op;
};

Sort BoolectorTerm::get_sort() const
{
  Sort sort;
  BoolectorSort s = boolector_get_sort(btor, node);
  if (boolector_is_bitvec_sort(btor, s))
  {
    uint64_t width = boolector_get_width(btor, node);
    // increment reference counter for the sort
    boolector_copy_sort(btor, s);
    sort = std::make_shared<BoolectorBVSort>(btor, s, width);
  }
  else if (boolector_is_array_sort(btor, s))
  {
    uint64_t idxwidth = boolector_get_index_width(btor, node);
    uint64_t elemwidth = boolector_get_width(btor, node);
    // Note: Boolector does not support multidimensional arrays
    std::shared_ptr<BoolectorSortBase> idxsort =
        std::make_shared<BoolectorBVSort>(
            btor, boolector_bitvec_sort(btor, idxwidth), idxwidth);
    std::shared_ptr<BoolectorSortBase> elemsort =
        std::make_shared<BoolectorBVSort>(
            btor, boolector_bitvec_sort(btor, elemwidth), elemwidth);
    // increment reference counter for the sort
    boolector_copy_sort(btor, s);
    sort = std::make_shared<BoolectorArraySort>(btor, s, idxsort, elemsort);
  }
  // FIXME : combine all sorts into one class -- easier that way
  // else if(boolector_is_fun_sort(btor, s))
  // {
  //   // FIXME: what if the arity is not one -- no way to get the domain sorts
  //   in current boolector api if (boolector_get_fun_arity(btor, node) != 1)
  //   {
  //     throw NotImplementedException("Boolector does not support getting
  //     multiple domain sorts yet.");
  //   }
  //   Sort ds = boolector_fun_get_domain_sort(btor, node);
  //   Sort cds = boolector_fun_get_codomain_sort(btor, node);
  //   sort = std::make_shared<BoolectorUFSort>(btor, s,
  //   std::vector<BoolectorSort>{ds}, cds);
  // }
  else
  {
    Unreachable();
  }
  return sort;
}

bool BoolectorTerm::is_symbol() const
{
  // functions, parameters, and symbolic constants are all symbols
  auto bkind = bn->kind;
  return !negated
         && ((bkind == BTOR_VAR_NODE) || (bkind == BTOR_UF_NODE)
             || (bkind == BTOR_PARAM_NODE));
}

bool BoolectorTerm::is_param() const
{
  return !negated && (bn->kind == BTOR_PARAM_NODE);
}

bool BoolectorTerm::is_symbolic_const() const
{
  // symbolic constant if it's a symbol but not a function
  // or a parameter
  // Important Note: Arrays are functions in boolector
  // Thus, we need to check whether it's a function or an array
  // because arrays should still be considered symbolic constants
  // in smt-switch
  bool is_fun = boolector_is_fun(btor, node) && !boolector_is_array(btor, node);
  return !is_fun && !is_param() && is_symbol();
}

bool BoolectorTerm::is_value() const
{
  bool res = boolector_is_const(btor, node);
  // constant arrays are considered values
  res |= is_const_array();
  return res;
}

std::string BoolectorTerm::to_string()
{
  std::string sres;

  // don't pointer chase!
  char * sym = btor_node_get_symbol(btor, BTOR_IMPORT_BOOLECTOR_NODE(node));

  if (sym)
  {
    // has a symbol
    if (negated)
    {
      sres = std::string("(bvnot ") + sym + ")";
    }
    else
    {
      sres = sym;
    }
    return sres;
  }
  else if (boolector_is_const(btor, node))
  {
    const char * btor_cstr = boolector_get_bits(btor, node);
    sres = "#b" + std::string(btor_cstr);
    boolector_free_bits(btor, btor_cstr);
    return sres;
  }
  else
  {
    // just print smt-lib
    // won't necessarily use symbol names (might use auxiliary variables)
    char * cres;
    size_t size;
    FILE * stream = open_memstream(&cres, &size);
    boolector_dump_smt2_node(btor, stream, node);
    int64_t status = fflush(stream);
    if (status != 0)
    {
      throw InternalSolverException("Error flushing stream for btor to_string");
    }
    status = fclose(stream);
    if (status != 0)
    {
      throw InternalSolverException("Error closing stream for btor to_string");
    }
    sres = cres;
    free(cres);
    return sres;
  }
}

uint64_t BoolectorTerm::to_int() const
{
  if (!boolector_is_const(btor, node))
  {
    throw IncorrectUsageException(
        "Can't get bitstring from a non-constant term.");
  }
  const char * assignment = boolector_bv_assignment(btor, node);
  std::string s(assignment);
  boolector_free_bv_assignment(btor, assignment);
  uint32_t width = boolector_get_width(btor, node);
  if (width > 64)
  {
    std::string msg("Can't represent a bit-vector of size ");
    msg += std::to_string(width);
    msg += " in a uint64_t";
    throw IncorrectUsageException(msg.c_str());
  }
  std::string::size_type sz = 0;
  return std::stoull(s, &sz, 2);
}

/** Iterators for traversing the children
 */
TermIter BoolectorTerm::begin()
{
  collect_children();
  return TermIter(new BoolectorTermIter(btor, children, 0));
}

TermIter BoolectorTerm::end()
{
  collect_children();
  return TermIter(new BoolectorTermIter(btor, children, children.size()));
}

std::string BoolectorTerm::print_value_as(SortKind sk)
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Cannot use print_value_as on a non-value term.");
  }

  BoolectorSort s = boolector_get_sort(btor, node);
  if (boolector_is_bitvec_sort(btor, s))
  {
    uint64_t width = boolector_get_width(btor, node);
    if (width == 1 && sk == BOOL)
    {
      const char * charval = boolector_get_bits(btor, node);
      std::string bits = charval;
      boolector_free_bv_assignment(btor, charval);
      if (bits == "1")
      {
        return "true";
      }
      else
      {
        return "false";
      }
    }
    else
    {
      return to_string();
    }
  }
  else
  {
    return to_string();
  }
}

// helpers

bool BoolectorTerm::is_const_array() const
{
  return ((bn->kind == BTOR_LAMBDA_NODE) && (bn->is_array));
}

void BoolectorTerm::collect_children()
{
  if (btor_node_is_proxy(bn))
  {
    bn = btor_node_get_simplified(btor, bn);
    bn = btor_node_real_addr(bn);
  }
  else if (children_cached_)
  {
    // children have already been computed on an updated node
    // can't do this if negated, because arity won't match
    // boolector will say 0 because it's not considered an operator
    // but in smt-switch we'd want one child
    return;
  }

  if (negated)
  {
    // the negated value is the real address stored in bn
    children.clear();
    children.push_back(bn);
    return;
  }

  children.clear();
  BtorNode * tmp;
  // don't expose the parameter node of the lambda -- start at 1 instead of 0
  size_t start_idx = is_const_array() ? 1 : 0;
  assert(!is_const_array() || bn->e[0]->kind == BTOR_PARAM_NODE);
  for (size_t i = start_idx; i < bn->arity; ++i)
  {
    tmp = bn->e[i];
    // a non-proxy node should never have proxy children
    assert(!btor_node_is_proxy(tmp));
    if (btor_node_real_addr(tmp)->kind == BTOR_ARGS_NODE)
    {
      btor_iter_args_init(&ait, tmp);
      while (btor_iter_args_has_next(&ait))
      {
        children.push_back(btor_iter_args_next(&ait));
      }
    }
    else
    {
      children.push_back(tmp);
    }
  }

  children_cached_ = true;
}

/* end BoolectorTerm implementation */

}  // namespace smt
