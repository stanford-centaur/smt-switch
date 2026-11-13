/*!
 * \file boolector_term.cpp
 * \brief Boolector implementation of AbsTerm
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/boolector_term.h"

#include <boolector.h>

extern "C" {
#include <btorcore.h>
#include <btornode.h>
#include <btorsort.h>
#include <utils/btornodeiter.h>
}

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <string>
#include <string_view>

#include "smt-switch/boolector_sort.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/utils.h"

namespace smt {

// helpers

/** The PrimOp of the nodes of kind k, or NUM_OPS_AND_NULL for a kind whose
 *  nodes are not applications
 *  @throws SmtException for a kind with no PrimOp
 */
static PrimOp primop_of(BtorNodeKind k)
{
  switch (k)
  {
    case BTOR_BV_CONST_NODE: return NUM_OPS_AND_NULL;
    case BTOR_VAR_NODE: return NUM_OPS_AND_NULL;
    case BTOR_PARAM_NODE: return NUM_OPS_AND_NULL;
    case BTOR_BV_SLICE_NODE: return Extract;
    case BTOR_BV_AND_NODE: return BVAnd;
    // BVComp makes the same node, but Equal is the more common reading.
    case BTOR_BV_EQ_NODE: return Equal;
    case BTOR_FUN_EQ_NODE: return Equal;
    case BTOR_BV_ADD_NODE: return BVAdd;
    case BTOR_BV_MUL_NODE: return BVMul;
    case BTOR_BV_ULT_NODE: return BVUlt;
    case BTOR_BV_SLL_NODE: return BVShl;
    case BTOR_BV_SRL_NODE: return BVLshr;
    case BTOR_BV_UDIV_NODE: return BVUdiv;
    case BTOR_BV_UREM_NODE: return BVUrem;
    case BTOR_BV_CONCAT_NODE: return Concat;
    case BTOR_APPLY_NODE: return Apply;
    case BTOR_FORALL_NODE: return Forall;
    case BTOR_EXISTS_NODE: return Exists;
    case BTOR_COND_NODE: return Ite;
    case BTOR_UF_NODE: return NUM_OPS_AND_NULL;
    case BTOR_UPDATE_NODE: return Store;
    default:
      throw SmtException("smt-switch has no PrimOp for the Boolector node kind "
                         + std::to_string(k));
  }
}

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
    op = Op(Extract,
            btor_node_bv_slice_get_upper(bn),
            btor_node_bv_slice_get_lower(bn));
  }
  else if ((k == BTOR_LAMBDA_NODE) && (bn->is_array))
  {
    // constant array is a value -- give it a null operator
    op = Op();
  }
  else
  {
    op = Op(primop_of(k));
  }
  return op;
}

/* BoolectorTerm implementation */

BoolectorTerm::BoolectorTerm(const std::shared_ptr<Btor> & b, BoolectorNode * n)
    : btor(b), node(n), bn(btor_node_real_addr(BTOR_IMPORT_BOOLECTOR_NODE(n)))
{
  // a substituted symbol becomes a proxy that keeps only its name, and only
  // symbols are named
  BtorNode * exp = BTOR_IMPORT_BOOLECTOR_NODE(n);
  BtorNodeKind k = bn->kind;
  // functions, parameters, and symbolic constants are all symbols
  symbol =
      btor_node_is_regular(exp)
      && ((k == BTOR_VAR_NODE) || (k == BTOR_UF_NODE) || (k == BTOR_PARAM_NODE)
          || ((k == BTOR_PROXY_NODE) && btor_node_get_symbol(btor.get(), exp)));
  if (!symbol && btor_node_is_proxy(bn))
  {
    bn = btor_node_real_addr(btor_node_get_simplified(btor.get(), bn));
  }
}

BoolectorTerm::~BoolectorTerm()
{
  release_children();
  boolector_release(btor.get(), node);
}

// BoolectorNode * -> id

std::size_t BoolectorTerm::hash() const
{
  return reinterpret_cast<std::size_t>(node);
}

std::size_t BoolectorTerm::get_id() const
{
  return reinterpret_cast<std::size_t>(node);
}

bool BoolectorTerm::compare(const Term & absterm) const
{
  std::shared_ptr<BoolectorTerm> other =
      std::dynamic_pointer_cast<BoolectorTerm>(absterm);
  return other && this->node == other->node;
}

bool BoolectorTerm::is_negated() const
{
  BtorNode * exp = BTOR_IMPORT_BOOLECTOR_NODE(node);
  bool inverted = btor_node_is_inverted(exp);
  BtorNode * real = btor_node_real_addr(exp);
  // The node a proxy stands for can itself be inverted, as when x := #b1111
  // leaves the xor of x and y as the negation of y.
  if (!symbol && btor_node_is_proxy(real))
  {
    BtorNode * simplified = btor_node_get_simplified(btor.get(), real);
    inverted = inverted != btor_node_is_inverted(simplified);
    real = btor_node_real_addr(simplified);
  }
  return inverted && real->kind != BTOR_BV_CONST_NODE;
}

Op BoolectorTerm::get_op() const
{
  Op op;

  if (is_negated())
  {
    op = Op(BVNot);
  }
  else if (!symbol)
  {
    op = lookup_op(btor.get(), node);
  }

  return op;
}

Sort BoolectorTerm::get_sort() const
{
  Sort sort;
  BoolectorSort s = boolector_get_sort(btor.get(), node);
  // increment reference counter for the sort
  boolector_copy_sort(btor.get(), s);
  if (boolector_is_bitvec_sort(btor.get(), s))
  {
    uint64_t width = boolector_bitvec_sort_get_width(btor.get(), s);
    sort = std::make_shared<BoolectorBVSort>(btor, s, width);
  }
  // a unary function has the sort of the matching array, so ask the node
  else if (boolector_is_array(btor.get(), node))
  {
    uint32_t idxwidth = boolector_get_index_width(btor.get(), node);
    uint32_t elemwidth = boolector_get_width(btor.get(), node);
    // Note: Boolector does not support multidimensional arrays
    std::shared_ptr<BoolectorSortBase> idxsort =
        std::make_shared<BoolectorBVSort>(
            btor, boolector_bitvec_sort(btor.get(), idxwidth), idxwidth);
    std::shared_ptr<BoolectorSortBase> elemsort =
        std::make_shared<BoolectorBVSort>(
            btor, boolector_bitvec_sort(btor.get(), elemwidth), elemwidth);
    sort = std::make_shared<BoolectorArraySort>(btor, s, idxsort, elemsort);
  }
  else if (boolector_is_fun_sort(btor.get(), s))
  {
    BoolectorSort bcds = boolector_fun_get_codomain_sort(btor.get(), node);
    uint64_t bcds_width = boolector_bitvec_sort_get_width(btor.get(), bcds);
    // increment reference counter for the sort
    boolector_copy_sort(btor.get(), bcds);
    Sort cds = std::make_shared<BoolectorBVSort>(btor, bcds, bcds_width);

    // Boolector's domain is a tuple sort, even of one element, and its API
    // cannot unpack one, so the elements are read internally
    SortVec domain_sorts;
    BtorTupleSortIterator it;
    btor_iter_tuple_sort_init(
        &it,
        btor.get(),
        btor_sort_fun_get_domain(btor.get(), BTOR_IMPORT_BOOLECTOR_SORT(s)));
    while (btor_iter_tuple_sort_has_next(&it))
    {
      uint32_t bds_width =
          btor_sort_bv_get_width(btor.get(), btor_iter_tuple_sort_next(&it));
      domain_sorts.push_back(std::make_shared<BoolectorBVSort>(
          btor, boolector_bitvec_sort(btor.get(), bds_width), bds_width));
    }
    sort = std::make_shared<BoolectorUFSort>(btor, s, domain_sorts, cds);
  }
  else
  {
    throw SmtException(
        "Failed to translate a Boolector sort to an smt-switch sort");
  }

  return sort;
}

bool BoolectorTerm::is_symbol() const { return symbol; }

bool BoolectorTerm::is_param() const
{
  return !is_negated() && (bn->kind == BTOR_PARAM_NODE);
}

bool BoolectorTerm::is_symbolic_const() const
{
  // symbolic constant if it's a symbol but not a function
  // or a parameter
  // Important Note: Arrays are functions in boolector
  // Thus, we need to check whether it's a function or an array
  // because arrays should still be considered symbolic constants
  // in smt-switch
  bool is_fun = boolector_is_fun(btor.get(), node)
                && !boolector_is_array(btor.get(), node);
  return !is_fun && !is_param() && is_symbol();
}

bool BoolectorTerm::is_value() const
{
  if (bn->kind == BTOR_UPDATE_NODE)
  {
    // SMT-LIB's ArraysEx makes a store of a value into an array value a value
    for (const Term & c : *this)
    {
      if (!c->is_value())
      {
        return false;
      }
    }
    return true;
  }
  bool res = boolector_is_const(btor.get(), node);
  // constant arrays are considered values
  res |= is_const_array();
  return res;
}

/** Returns the bits of a constant, most significant first */
static std::string const_to_bits(Btor * btor, BoolectorNode * node)
{
  if (!boolector_is_const(btor, node))
  {
    throw IncorrectUsageException(
        "Can't get a bitstring from a term that is not a constant");
  }
  // the bits of the constant itself, which need no model, unlike its
  // assignment
  const char * bits = boolector_get_bits(btor, node);
  std::string s;
  try
  {
    s = bits;
  }
  catch (...)
  {
    boolector_free_bits(btor, bits);
    throw;
  }
  boolector_free_bits(btor, bits);
  return s;
}

namespace {

struct MallocDeleter
{
  void operator()(char * p) const { std::free(p); }
};

}  // namespace

std::string BoolectorTerm::to_string() const
{
  std::string sres;

  // don't pointer chase!
  char * sym =
      btor_node_get_symbol(btor.get(), BTOR_IMPORT_BOOLECTOR_NODE(node));
  // Boolector dumps a declaration for a node that simplifies to a symbol, so
  // the symbol is printed instead.
  if (!sym)
  {
    BtorNode * simplified =
        btor_node_get_simplified(btor.get(), BTOR_IMPORT_BOOLECTOR_NODE(node));
    if (btor_node_is_bv_var(simplified) || btor_node_is_uf(simplified))
    {
      sym = btor_node_get_symbol(btor.get(), simplified);
    }
  }

  if (sym)
  {
    // has a symbol
    if (is_negated())
    {
      sres = std::string("(bvnot ") + sym + ")";
    }
    else
    {
      sres = sym;
    }
    return sres;
  }
  else if (boolector_is_const(btor.get(), node))
  {
    return "#b" + const_to_bits(btor.get(), node);
  }
  else
  {
    // just print smt-lib
    // won't necessarily use symbol names (might use auxiliary variables)
    char * cres = nullptr;
    size_t size = 0;
    FILE * stream = open_memstream(&cres, &size);
    if (!stream)
    {
      throw InternalSolverException(
          "Failed to open a stream for Boolector's to_string");
    }
    try
    {
      boolector_dump_smt2_node(btor.get(), stream, node);
    }
    catch (...)
    {
      fclose(stream);
      std::free(cres);
      throw;
    }
    // closing flushes the stream, and leaves the buffer to free even if it
    // fails
    int status = fclose(stream);
    std::unique_ptr<char, MallocDeleter> buffer(cres);
    if (status != 0)
    {
      throw InternalSolverException(
          "Failed to close the stream for Boolector's to_string");
    }
    return buffer.get();
  }
}

std::string BoolectorTerm::get_constructor_name() const
{
  throw IncorrectUsageException(
      "Only a constructor or a tester has a constructor name");
}

std::string BoolectorTerm::get_param_name() const
{
  if (!is_param())
  {
    throw IncorrectUsageException("Only a param has a param name");
  }
  // make_param names it internal_name("param", n), an underscore, then the
  // name it was given
  std::string internal =
      btor_node_get_symbol(btor.get(), BTOR_IMPORT_BOOLECTOR_NODE(node));
  std::size_t number =
      INTERNAL_NAME_PREFIX.size() + std::string_view("param_").size();
  return internal.substr(internal.find('_', number) + 1);
}

std::string BoolectorTerm::get_selector_name() const
{
  throw IncorrectUsageException("Only a selector has a selector name");
}

std::string BoolectorTerm::get_symbol_name() const
{
  if (!symbol || is_param())
  {
    throw IncorrectUsageException(
        "Only a symbol that is not a param has a symbol name");
  }
  // A substituted symbol is a proxy, which keeps the name.
  return btor_node_get_symbol(btor.get(), BTOR_IMPORT_BOOLECTOR_NODE(node));
}

uint64_t BoolectorTerm::to_int() const
{
  return bits_to_uint64(const_to_bits(btor.get(), node));
}

int64_t BoolectorTerm::to_signed_int() const
{
  return bits_to_int64(const_to_bits(btor.get(), node));
}

bool BoolectorTerm::to_bool() const
{
  // Boolector makes Booleans 1-bit bit-vectors
  BoolectorSort s = boolector_get_sort(btor.get(), node);
  if (!boolector_is_const(btor.get(), node)
      || !boolector_is_bitvec_sort(btor.get(), s)
      || boolector_get_width(btor.get(), node) != 1)
  {
    throw IncorrectUsageException("Can't convert " + to_string()
                                  + " to a Boolean: it is not a Boolean value");
  }
  return const_to_bits(btor.get(), node) == "1";
}

std::size_t BoolectorTerm::get_num_children() const
{
  collect_children();
  return children.size();
}

Term BoolectorTerm::get_child(std::size_t i) const
{
  // Boolector can simplify the node after an iterator counted its children,
  // and collecting them again for another iterator can leave fewer.
  if (i >= children.size())
  {
    throw IncorrectUsageException(
        "The term's children changed since the iterator was made");
  }
  BtorNode * res = children[i];
  if (btor_node_real_addr(res)->kind == BTOR_ARGS_NODE)
  {
    throw SmtException("Boolector gave an args node as a child");
  }

  // increment internal reference counter
  res = btor_node_copy(btor.get(), res);
  // increment external reference counter
  btor_node_inc_ext_ref_counter(btor.get(), res);

  BoolectorNode * child = BTOR_EXPORT_BOOLECTOR_NODE(res);
  return std::make_shared<BoolectorTerm>(btor, child);
}

std::string BoolectorTerm::print_value_as(SortKind sk) const
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Can't use print_value_as on a term that is not a value");
  }

  BoolectorSort s = boolector_get_sort(btor.get(), node);
  if (boolector_is_bitvec_sort(btor.get(), s))
  {
    uint64_t width = boolector_get_width(btor.get(), node);
    if (width == 1 && sk == BOOL)
    {
      if (const_to_bits(btor.get(), node) == "1")
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

BoolectorNode * BoolectorTerm::get_btor_node() const { return node; }

// helpers

bool BoolectorTerm::is_const_array() const
{
  return ((bn->kind == BTOR_LAMBDA_NODE) && (bn->is_array));
}

void BoolectorTerm::collect_children() const
{
  // a substituted symbol is still a leaf, so its proxy is not followed
  if (!symbol && btor_node_is_proxy(bn))
  {
    bn = btor_node_get_simplified(btor.get(), bn);
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

  release_children();
  if (is_negated())
  {
    // the negated value is the real address stored in bn
    children.push_back(btor_node_copy(btor.get(), bn));
    return;
  }

  BtorNode * tmp;
  // don't expose the parameter node of the lambda -- start at 1 instead of 0
  size_t start_idx = is_const_array() ? 1 : 0;
  for (size_t i = start_idx; i < bn->arity; ++i)
  {
    tmp = bn->e[i];
    if (btor_node_real_addr(tmp)->kind == BTOR_ARGS_NODE)
    {
      btor_iter_args_init(&ait, tmp);
      while (btor_iter_args_has_next(&ait))
      {
        children.push_back(
            btor_node_copy(btor.get(), btor_iter_args_next(&ait)));
      }
    }
    else
    {
      children.push_back(btor_node_copy(btor.get(), tmp));
    }
  }

  children_cached_ = true;
}

void BoolectorTerm::release_children() const
{
  for (BtorNode * n : children)
  {
    btor_node_release(btor.get(), n);
  }
  children.clear();
}

/* end BoolectorTerm implementation */

}  // namespace smt
