#include "boolector_term.h"

namespace smt {

/* BoolectorTermIter implementation */

BoolectorTermIter & BoolectorTermIter::operator=(const BoolectorTermIter & it)
{
  v_it = it.v_it;
  return *this;
};

void BoolectorTermIter::operator++() { v_it++; };

void BoolectorTermIter::operator++(int junk) { v_it++; };

const Term BoolectorTermIter::operator*() const { return *v_it; };

bool BoolectorTermIter::operator==(const BoolectorTermIter & it)
{
  return v_it == it.v_it;
};

bool BoolectorTermIter::operator!=(const BoolectorTermIter & it)
{
  return v_it != it.v_it;
};

bool BoolectorTermIter::equal(const TermIterBase & other) const
{
  // guaranteed to be safe by caller of equal (TermIterBase)
  const BoolectorTermIter & bti = static_cast<const BoolectorTermIter &>(other);
  return v_it == bti.v_it;
}

/* end BoolectorTermIter implementation */

/* BoolectorTerm implementation */

BoolectorTerm::~BoolectorTerm() { boolector_release(btor, node); }

// TODO: check if this is okay -- probably not
std::size_t BoolectorTerm::hash() const
{
  return (std::size_t)boolector_get_node_id(btor, node);
};

bool BoolectorTerm::compare(const Term & absterm) const
{
  std::shared_ptr<BoolectorTerm> other =
      std::static_pointer_cast<BoolectorTerm>(absterm);
  return boolector_get_node_id(this->btor, this->node)
         == boolector_get_node_id(other->btor, other->node);
}

Fun BoolectorTerm::get_fun() const { return f; };

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
  else
  {
    Unreachable();
  }
  return sort;
}

bool BoolectorTerm::is_symbolic_const() const
{
  return boolector_is_var(btor, node);
}

bool BoolectorTerm::is_interpreted_const() const
{
  return boolector_is_const(btor, node);
}

std::string BoolectorTerm::to_string() const
{
  try
  {
    const char * btor_symbol = boolector_get_symbol(btor, node);
    std::string symbol(btor_symbol);
    return symbol;
  }
  catch (std::logic_error & e)
  {
    return "btor_expr";
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
  return TermIter(new BoolectorTermIter(children.begin()));
}

TermIter BoolectorTerm::end()
{
  return TermIter(new BoolectorTermIter(children.end()));
}

/* end BoolectorTerm implementation */

}  // namespace smt
