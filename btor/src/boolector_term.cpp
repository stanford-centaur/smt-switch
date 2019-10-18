#include "boolector_term.h"

// include standard version of open_memstream
// for compatability with FreeBSD / Darwin which doesn't support it natively
extern "C"
{
#include "memstream.h"
}

#include <unordered_map>
#include "stdio.h"

namespace smt {

/* global variables */
const std::unordered_map<BtorNodeKind, PrimOp> btorkind2primop({
    //{BTOR_INVALID_NODE}, // this should never happen
    { BTOR_BV_CONST_NODE, NUM_OPS_AND_NULL },
    { BTOR_VAR_NODE, NUM_OPS_AND_NULL },
    { BTOR_PARAM_NODE, NUM_OPS_AND_NULL },
    { BTOR_BV_SLICE_NODE, Extract },
    { BTOR_BV_AND_NODE, BVAnd },
    { BTOR_BV_EQ_NODE, BVComp },
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
    // {BTOR_FORALL_NODE}, // TODO: implement later
    // {BTOR_EXISTS_NODE}, // TODO: implement later
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
    bn = btor_node_real_addr(btor_pointer_chase_simplified_exp(btor, bn));
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
    op = Op(Const_Array);
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

void BoolectorTermIter::operator++(int junk) { idx++; };

const Term BoolectorTermIter::operator*()
{
  BtorNode * res = children[idx];
  if (btor_node_real_addr(res)->kind == BTOR_ARGS_NODE)
  {
    throw SmtException("Should never have an args node in children look up");
  }

  // need to increment reference counter, because accessing child doesn't
  // increment it
  //  but BoolectorTerm destructor will release it
  // use real_addr?
  if (!btor_node_real_addr(res)->ext_refs)
  {
    if (btor_node_is_proxy(res))
    {
      res = btor_pointer_chase_simplified_exp(btor, res);
    }
    btor_node_inc_ext_ref_counter(btor, res);
  }

  BoolectorNode * node = boolector_copy(btor, BTOR_EXPORT_BOOLECTOR_NODE(res));
  Term t(new BoolectorTerm(btor, node));
  return t;
};

bool BoolectorTermIter::operator==(const BoolectorTermIter & it)
{
  return ((btor == it.btor) && (idx == it.idx));
};

bool BoolectorTermIter::operator!=(const BoolectorTermIter & it)
{
  return ((btor != it.btor) || (idx != it.idx));
};

bool BoolectorTermIter::equal(const TermIterBase & other) const
{
  // guaranteed to be safe by caller of equal (TermIterBase)
  const BoolectorTermIter & bti = static_cast<const BoolectorTermIter &>(other);
  return ((btor == bti.btor) && (idx == bti.idx));
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
    bn = btor_node_real_addr(btor_pointer_chase_simplified_exp(btor, bn));
  }
  negated = (((((uintptr_t)node) % 2) != 0) && bn->kind != BTOR_BV_CONST_NODE);
  is_sym =
      !negated && ((bn->kind == BTOR_VAR_NODE) || (bn->kind == BTOR_UF_NODE));
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
    unsigned int width = boolector_get_width(btor, node);
    // increment reference counter for the sort
    boolector_copy_sort(btor, s);
    sort = std::make_shared<BoolectorBVSort>(btor, s, width);
  }
  else if (boolector_is_array_sort(btor, s))
  {
    unsigned int idxwidth = boolector_get_index_width(btor, node);
    unsigned int elemwidth = boolector_get_width(btor, node);
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

bool BoolectorTerm::is_symbolic_const() const
{
  return is_sym;
}

bool BoolectorTerm::is_value() const
{
  bool res = boolector_is_const(btor, node);
  // constant arrays are considered values
  res |= is_const_array();
  return res;
}

std::string BoolectorTerm::to_string() const
{
  std::string sres;

  // don't pointer chase!
  char * sym = btor_node_get_symbol(btor, BTOR_IMPORT_BOOLECTOR_NODE(node));

  if (sym)
  {
    // has a symbol
    sres = sym;
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
    int status = fflush(stream);
    if (status != 0)
    {
      std::cout << "got error code flushing: " << status << std::endl;
    }
    status = fclose(stream);
    if (status != 0)
    {
      std::cout << "got error code closing: " << status << std::endl;
    }
    sres = cres;
    free(cres);
    free(stream);
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
  if (btor_node_is_proxy(bn))
  {
    bn = btor_pointer_chase_simplified_exp(btor, bn);
  }

  children.clear();
  BtorNode * tmp;
  for (size_t i = 0; i < bn->arity; ++i)
  {
    tmp = bn->e[i];
    // TODO: figure out if should we do this?
    // if (btor_node_is_proxy(tmp))
    // {
    //   tmp = btor_pointer_chase_simplified_exp(btor, tmp);
    // }
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

  if (negated)
  {
    // the negated value is the real address stored in bn
    children.clear();
    children.push_back(bn);
    return TermIter(new BoolectorTermIter(btor, children, 0));
  }
  else if (is_const_array())
  {
    // constant array case
    // don't expose the parameter node of the lambda -- start at 1 instead of 0
    return TermIter(new BoolectorTermIter(btor, children, 1));
  }
  else
  {
    return TermIter(new BoolectorTermIter(btor, children, 0));
  }
}

TermIter BoolectorTerm::end()
{
  if (btor_node_is_proxy(bn))
  {
    bn = btor_pointer_chase_simplified_exp(btor, bn);
  }

  if (negated)
  {
    BtorNode * e[3];
    // the negated value is the real address stored in bn
    e[0] = bn;
    // vector doesn't matter for end
    return TermIter(new BoolectorTermIter(btor, std::vector<BtorNode *>{}, 1));
  }
  else
  {
    BtorNode * tmp;
    int num_children = 0;
    for (size_t i = 0; i < bn->arity; ++i)
    {
      tmp = bn->e[i];
      // TODO: figure out if should we do this?
      // if (btor_node_is_proxy(tmp))
      // {
      //   tmp = btor_pointer_chase_simplified_exp(btor, tmp);
      // }
      // flatten args nodes (chains of arguments)
      if (btor_node_real_addr(tmp)->kind == BTOR_ARGS_NODE)
      {
        btor_iter_args_init(&ait, tmp);
        while (btor_iter_args_has_next(&ait))
        {
          btor_iter_args_next(&ait);
          num_children++;
        }
      }
      else
      {
        num_children++;
      }
    }
    // vector doesn't matter for end
    return TermIter(
        new BoolectorTermIter(btor, std::vector<BtorNode *>{}, num_children));
  }
}

// helpers

bool BoolectorTerm::is_const_array() const
{
  return ((bn->kind == BTOR_LAMBDA_NODE) && (bn->is_array));
}

/* end BoolectorTerm implementation */

}  // namespace smt
