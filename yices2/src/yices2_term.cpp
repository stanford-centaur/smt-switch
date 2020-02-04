#include "yices2_term.h"
#include "exceptions.h"
#include "ops.h"
#include "yices2_sort.h"

#include <unordered_map>

using namespace std;

namespace smt {

// Yices2TermIter implementation

Yices2TermIter::Yices2TermIter(const Yices2TermIter & it)
{
  term = it.term;
  pos = it.pos;
}

Yices2TermIter & Yices2TermIter::operator=(const Yices2TermIter & it)
{
  term = it.term;
  pos = it.pos;
  return *this;
}

void Yices2TermIter::operator++() { pos++; }

const Term Yices2TermIter::operator*()
{
  uint32_t actual_idx = pos - 1;

  if (yices_term_is_function(term))
  {
    if (!pos)
    {
      return Term(new Yices2Term(term));
    }
    else
    {
      return Term(new Yices2Term(yices_term_child(term, actual_idx)));
    }
  }
  // Must handle polynomial format for bv sums.
  // See Yices documentation for yices_bvsum_component
  else if (yices_term_is_bvsum(term))
  {
    term_t component;
    uint64_t w = (Term(new Yices2Term(term))->get_sort()->get_width());
    int32_t val[w];
    yices_bvsum_component(term, pos, val, &component);
    if (component != NULL_TERM)
    {
      return Term(new Yices2Term(
          yices_bvmul(yices_bvconst_from_array(w, val), component)));
    }
    else
    {
      return Term(new Yices2Term(yices_bvconst_from_array(w, val)));
    }
  }
  // Must handle polynomial format for sums.
  else if (yices_term_is_sum(term))
  {
    term_t component;
    mpq_t coeff;
    mpq_init(coeff);

    // Special case for term components like (* -1 b),
    // which, according to the Yices API, is an arithmetic sum.
    // So yices_term_is_sum(term) will return true, and the
    // number of children is 1.
    if (yices_term_num_children(term) == 1)
    {
      if (!pos)
      {
        yices_sum_component(term, pos, coeff, &component);
        return Term(new Yices2Term(yices_mpq(coeff)));
      }
      else
      {
        yices_sum_component(term, actual_idx, coeff, &component);
        return Term(new Yices2Term(component));
      }
    }
    else
    {
      yices_sum_component(term, pos, coeff, &component);
      if (component != NULL_TERM)
      {
        return Term(new Yices2Term(yices_mul(component, yices_mpq(coeff))));
      }
      // Something like (+ 100 x) will have the 100 represented
      // as (+ (* 100 NULL_TERM) (* 1 x))
      else
      {
        return Term(new Yices2Term(yices_mpq(coeff)));
      }
    }
  }
  // Must handle polynomial format for products.
  // See Yices documentation for yices_product_component
  else if (yices_term_is_product(term))
  {
    term_t component;
    uint32_t exp;
    // Special case similar to sum case to handle
    // terms like (^ b 4).
    if (yices_term_num_children(term) == 1)
    {
      if (!pos)
      {
        yices_product_component(term, pos, &component, &exp);
        return Term(new Yices2Term(component));
      }
      else
      {
        yices_product_component(term, actual_idx, &component, &exp);
        return Term(new Yices2Term(yices_int64(exp)));
      }
    }

    yices_product_component(term, pos, &component, &exp);

    if (exp != 1)
    {
      return Term(new Yices2Term(yices_power(component, exp)));
    }
    // If exp is one, just return the component. This is important
    // because the component may be an uninterpreted term, and
    // there will be an error if you try to call yices_power with
    // an uninterpreted term.
    else
    {
      return Term(new Yices2Term(component));
    }
  }
  else if (yices_term_is_composite(term))
  {
    return Term(new Yices2Term(yices_term_child(term, pos)));
  }
  else
  {
    return Term(new Yices2Term(term));
  }
}

bool Yices2TermIter::operator==(const Yices2TermIter & it)
{
  return ((term == it.term) && (pos == it.pos));
}

bool Yices2TermIter::operator!=(const Yices2TermIter & it)
{
  return ((term != it.term) || (pos != it.pos));
}

bool Yices2TermIter::equal(const TermIterBase & other) const
{
  const Yices2TermIter & cti = static_cast<const Yices2TermIter &>(other);
  return ((term == cti.term) && (pos == cti.pos));
}

// end Yices2TermIter implementation

// Yices2Term implementation

size_t Yices2Term::hash() const
{
  // term_t is a unique id for the term.
  return term;
}

bool Yices2Term::compare(const Term & absterm) const
{
  shared_ptr<Yices2Term> yterm = std::static_pointer_cast<Yices2Term>(absterm);
  return term == yterm->term;
}

Op Yices2Term::get_op() const
{
  term_constructor_t tc = yices_term_constructor(term);
  std::string sres;
  switch (tc)
  {
    // atomic terms
    case YICES_BOOL_CONSTANT:
    case YICES_ARITH_CONSTANT:
    case YICES_BV_CONSTANT:
    case YICES_SCALAR_CONSTANT:
    case YICES_VARIABLE:
    case YICES_UNINTERPRETED_TERM: return Op();
    // composite terms
    case YICES_ITE_TERM: return Op(Ite);
    case YICES_APP_TERM:
      if (!is_function)
      {
        return Op(Select);
      }
      return Op(Apply);

    case YICES_EQ_TERM: return Op(Equal);
    case YICES_DISTINCT_TERM: return Op(Distinct);
    case YICES_NOT_TERM: return Op(Not);
    case YICES_OR_TERM: return Op(Or);
    case YICES_XOR_TERM: return Op(Xor);
    case YICES_BV_DIV: return Op(BVUdiv);
    case YICES_BV_REM: return Op(BVUrem);
    case YICES_BV_SDIV: return Op(BVSdiv);
    case YICES_BV_SREM: return Op(BVSrem);
    case YICES_BV_SMOD: return Op(BVSmod);
    case YICES_BV_SHL: return Op(BVShl);
    case YICES_BV_LSHR: return Op(BVLshr);
    case YICES_BV_ASHR: return Op(BVAshr);
    case YICES_BV_GE_ATOM: return Op(BVUge);
    case YICES_BV_SGE_ATOM: return Op(BVSge);
    case YICES_ARITH_GE_ATOM: return Op(Ge);
    case YICES_ABS: return Op(Abs);
    case YICES_RDIV: return Op(Div);
    case YICES_IDIV: return Op(Div);
    case YICES_IMOD: return Op(Mod);
    // // sums
    case YICES_BV_SUM: return Op(BVAdd);
    case YICES_ARITH_SUM:
      /* Arithmetic sums are represented as polynomials,
       * and something like (+ a (-b)) is actually
       * (+ a (* -1 b)), but the individual component
       * (* -1 b) is still of type YICES_ARITH_SUM. To transfer this
       * term, you need to construct the multiply.
       */
      sres = this->to_string();
      sres = sres.substr(sres.find("(") + 1, sres.length());
      sres = sres.substr(0, sres.find(" "));
      if (yices_term_num_children(term) == 1 && sres == "*")
      {
        return Op(Mult);
      }
      return Op(Plus);
    // products
    case YICES_POWER_PRODUCT:
      sres = this->to_string();
      sres = sres.substr(sres.find("(") + 1, sres.length());
      sres = sres.substr(0, sres.find(" "));
      if (sres == "bv-mul")
      {
        return Op(BVMul);
      }
      if (sres == "*")
      {
        return Op(Mult);
      }
      return Op(Pow);
    case YICES_UPDATE_TERM:
    case YICES_TUPLE_TERM:
    case YICES_FORALL_TERM:
    case YICES_LAMBDA_TERM:
    case YICES_BV_ARRAY:
    case YICES_ARITH_ROOT_ATOM:
    case YICES_CEIL:
    case YICES_FLOOR:
    case YICES_IS_INT_ATOM:
    case YICES_DIVIDES_ATOM:
    // projections
    case YICES_SELECT_TERM:
    case YICES_BIT_TERM:
    default: return Op();
  }
}

Sort Yices2Term::get_sort() const
{
  if (yices_term_is_function(term))
  {
    // ARRAY
    if (!is_function)
    {
      return Sort(new Yices2Sort(yices_type_of_term(term)));
    }
    // FUNCTION
    else
    {
      return Sort(new Yices2Sort(yices_type_of_term(term), true));
    }
  }

  return Sort(new Yices2Sort(yices_type_of_term(term)));
}

bool Yices2Term::is_symbolic_const() const
{
  term_constructor_t tc = yices_term_constructor(term);
  return (
      (tc == YICES_UNINTERPRETED_TERM && yices_term_num_children(term) == 0));
}

bool Yices2Term::is_value() const
{
  term_constructor_t tc = yices_term_constructor(term);

  return (tc == YICES_BOOL_CONSTANT || tc == YICES_ARITH_CONSTANT
          || tc == YICES_BV_CONSTANT || tc == YICES_SCALAR_CONSTANT);
}

string Yices2Term::to_string() const
{
  return yices_term_to_string(term, 120, 1, 0);
}

uint64_t Yices2Term::to_int() const
{
  std::string val = yices_term_to_string(term, 120, 1, 0);

  // Process bit-vector format.
  if (yices_term_is_bitvector(term))
  {
    if (val.find("0b") == std::string::npos)
    {
      std::string msg = val;
      msg += " is not a constant term, can't convert to int.";
      throw IncorrectUsageException(msg.c_str());
    }
    try
    {
      return std::stoi(val.substr(val.find("b") + 1, val.length()), 0, 2);
    }
    catch (std::exception const & e)
    {
      std::string msg("Term ");
      msg += val;
      msg += " does not contain an integer representable by a machine int.";
      throw IncorrectUsageException(msg.c_str());
    }
  }

  // If not bit-vector, try parsing an int from the term.
  try
  {
    return std::stoi(val);
  }
  catch (std::exception const & e)
  {
    std::string msg("Term ");
    msg += val;
    msg += " does not contain an integer representable by a machine int.";
    throw IncorrectUsageException(msg.c_str());
  }
}

TermIter Yices2Term::begin() { return TermIter(new Yices2TermIter(term, 0)); }

TermIter Yices2Term::end()
{
  // Special cases for handling individual components of polynomials.
  if (this->get_op() == Mult && yices_term_num_children(term) == 1)
  {
    return TermIter(
        new Yices2TermIter(term, yices_term_num_children(term) + 1));
  }
  if (this->get_op() == Pow && yices_term_num_children(term) == 1)
  {
    return TermIter(
        new Yices2TermIter(term, yices_term_num_children(term) + 1));
  }

  return TermIter(new Yices2TermIter(term, yices_term_num_children(term)));
}

// end Yices2Term implementation

}  // namespace smt
