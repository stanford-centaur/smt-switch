#include "msat_term.h"
#include "msat_sort.h"

#include "exceptions.h"
#include "ops.h"

#include <unordered_map>

namespace std
{
  // defining hash for old compilers
  template<>
  struct hash<msat_symbol_tag>
  {
    size_t operator()(const msat_symbol_tag t) const
    {
      return static_cast<size_t>(t);
    }
  };
}

using namespace std;

namespace smt {

/* Op mappings */
const std::unordered_map<msat_symbol_tag, PrimOp> tag2op({
    { MSAT_TAG_AND, And },
    { MSAT_TAG_OR, Or },
    { MSAT_TAG_NOT, Not },
    { MSAT_TAG_IFF, Iff },
    { MSAT_TAG_PLUS, Plus },
    { MSAT_TAG_TIMES, Mult },
    { MSAT_TAG_DIVIDE, Div },
    { MSAT_TAG_FLOOR, To_Int },
    { MSAT_TAG_LEQ, Le },
    { MSAT_TAG_EQ, Equal },
    { MSAT_TAG_ITE, Ite },
    // { MSAT_TAG_INT_MOD_CONGR, Mod }, // this is not regular mod
    { MSAT_TAG_BV_CONCAT, Concat },
    { MSAT_TAG_BV_EXTRACT, Extract },
    { MSAT_TAG_BV_NOT, BVNot },
    { MSAT_TAG_BV_AND, BVAnd },
    { MSAT_TAG_BV_OR, BVOr },
    { MSAT_TAG_BV_XOR, BVXor },
    { MSAT_TAG_BV_ULT, BVUlt },
    { MSAT_TAG_BV_SLT, BVSlt },
    { MSAT_TAG_BV_ULE, BVUle },
    { MSAT_TAG_BV_SLE, BVSle },
    { MSAT_TAG_BV_COMP, BVComp },
    { MSAT_TAG_BV_NEG, BVNeg },
    { MSAT_TAG_BV_ADD, BVAdd },
    { MSAT_TAG_BV_SUB, BVSub },
    { MSAT_TAG_BV_MUL, BVMul },
    { MSAT_TAG_BV_UDIV, BVUdiv },
    { MSAT_TAG_BV_SDIV, BVSdiv },
    { MSAT_TAG_BV_UREM, BVUrem },
    { MSAT_TAG_BV_SREM, BVSrem },
    { MSAT_TAG_BV_LSHL, BVShl },
    { MSAT_TAG_BV_LSHR, BVLshr },
    { MSAT_TAG_BV_ASHR, BVAshr },
    { MSAT_TAG_BV_ROL, Rotate_Left },
    { MSAT_TAG_BV_ROR, Rotate_Right },
    { MSAT_TAG_BV_ZEXT, Zero_Extend },
    { MSAT_TAG_BV_SEXT, Sign_Extend },
    { MSAT_TAG_ARRAY_READ, Select },
    { MSAT_TAG_ARRAY_WRITE, Store },
    { MSAT_TAG_ARRAY_CONST, NUM_OPS_AND_NULL }, // Const Array is a value (no op)
    { MSAT_TAG_INT_TO_BV, Int_To_BV },
    { MSAT_TAG_INT_FROM_UBV, BV_To_Nat },
    // MSAT_TAG_FP_EQ,
    // MSAT_TAG_FP_LT,
    // MSAT_TAG_FP_LE,
    // MSAT_TAG_FP_NEG,
    // MSAT_TAG_FP_ADD,
    // MSAT_TAG_FP_SUB,
    // MSAT_TAG_FP_MUL,
    // MSAT_TAG_FP_DIV,
    // MSAT_TAG_FP_SQRT,
    // MSAT_TAG_FP_ABS,
    // MSAT_TAG_FP_MIN,
    // MSAT_TAG_FP_MAX,
    // MSAT_TAG_FP_CAST,
    // MSAT_TAG_FP_ROUND_TO_INT,
    // MSAT_TAG_FP_FROM_SBV,
    // MSAT_TAG_FP_FROM_UBV,
    // MSAT_TAG_FP_TO_BV,
    // MSAT_TAG_FP_AS_IEEEBV,
    // MSAT_TAG_FP_ISNAN,
    // MSAT_TAG_FP_ISINF,
    // MSAT_TAG_FP_ISZERO,
    // MSAT_TAG_FP_ISSUBNORMAL,
    // MSAT_TAG_FP_ISNORMAL,
    // MSAT_TAG_FP_ISNEG,
    // MSAT_TAG_FP_ISPOS,
    // MSAT_TAG_FP_FROM_IEEEBV,
    // smt-lib doesn't have this kind -- if we never create it can probably
    // ignore it MSAT_TAG_INT_FROM_SBV
});

// MsatTermIter implementation

MsatTermIter::MsatTermIter(const MsatTermIter & it)
{
  term = it.term;
  pos = it.pos;
}

MsatTermIter & MsatTermIter::operator=(const MsatTermIter & it)
{
  term = it.term;
  pos = it.pos;
  return *this;
}

void MsatTermIter::operator++() { pos++; }

const Term MsatTermIter::operator*()
{
  if (!pos && msat_term_is_uf(env, term))
  {
    return std::make_shared<MsatTerm> (env, msat_term_get_decl(term));
  }
  else
  {
    uint32_t actual_idx = pos;
    if (msat_term_is_uf(env, term))
    {
      actual_idx--;
    }
    return std::make_shared<MsatTerm>
        (env, msat_term_get_arg(term, actual_idx));
  }
}

TermIterBase * MsatTermIter::clone() const
{
  return new MsatTermIter(env, term, pos);
}

bool MsatTermIter::operator==(const MsatTermIter & it)
{
  // null terms mean you're iterating over a function symbol
  // it has no children, so the two iterators should be considered equal
  if (MSAT_ERROR_TERM(term) && MSAT_ERROR_TERM(it.term))
  {
    return true;
  }
  else if (MSAT_ERROR_TERM(term) || MSAT_ERROR_TERM(it.term))
  {
    throw SmtException("Undefined TermIter comparison (not from same term)");
  }
  return ((msat_term_id(term) == msat_term_id(it.term)) && (pos == it.pos));
}

bool MsatTermIter::operator!=(const MsatTermIter & it)
{
  // null terms mean you're iterating over a function symbol
  // it has no children, so the two iterators should be considered equal
  if (MSAT_ERROR_TERM(term) && MSAT_ERROR_TERM(it.term))
  {
    return false;
  }
  else if (MSAT_ERROR_TERM(term) || MSAT_ERROR_TERM(it.term))
  {
    throw SmtException("Undefined TermIter comparison (not from same term)");
  }

  return ((msat_term_id(term) != msat_term_id(it.term)) || (pos != it.pos));
}

bool MsatTermIter::equal(const TermIterBase & other) const
{
  const MsatTermIter & cti = static_cast<const MsatTermIter &>(other);

  // null terms mean you're iterating over a function symbol
  // it has no children, so the two iterators should be considered equal
  if (MSAT_ERROR_TERM(term) && MSAT_ERROR_TERM(cti.term))
  {
    return true;
  }
  else if (MSAT_ERROR_TERM(term) || MSAT_ERROR_TERM(cti.term))
  {
    throw SmtException("Undefined TermIter comparison (not from same term)");
  }
  return ((msat_term_id(term) == msat_term_id(cti.term)) && (pos == cti.pos));
}

// end MsatTermIter implementation

// MsatTerm implementation

size_t MsatTerm::hash() const
{
  if (!is_uf)
  {
    return msat_term_id(term);
  }
  else
  {
    return msat_decl_id(decl);
  }
}

bool MsatTerm::compare(const Term & absterm) const
{
  shared_ptr<MsatTerm> mterm = std::static_pointer_cast<MsatTerm>(absterm);
  if (is_uf ^ mterm->is_uf)
  {
    // can't be equal if one is a uf and the other is not
    return false;
  }
  else if (!is_uf)
  {
    return (msat_term_id(term) == msat_term_id(mterm->term));
  }
  else
  {
    return (msat_decl_id(decl) == msat_decl_id(mterm->decl));
  }
}

Op MsatTerm::get_op() const
{
  if (is_uf)
  {
    // uninterpreted function has no op
    return Op();
  }
  else if (msat_term_is_and(env, term))
  {
    return Op(And);
  }
  else if (msat_term_is_or(env, term))
  {
    return Op(Or);
  }
  else if (msat_term_is_not(env, term))
  {
    return Op(Not);
  }
  else if (msat_term_is_iff(env, term))
  {
    return Op(Iff);
  }
  else if (msat_term_is_term_ite(env, term))
  {
    return Op(Ite);
  }
  else if (msat_term_is_constant(env, term))
  {
    return Op();
  }
  else if (msat_term_is_uf(env, term))
  {
    return Op(Apply);
  }
  else if (msat_term_is_equal(env, term))
  {
    return Op(Equal);
  }
  else if (msat_term_is_leq(env, term))
  {
    return Op(Le);
  }
  else if (msat_term_is_plus(env, term))
  {
    return Op(Plus);
  }
  else if (msat_term_is_times(env, term))
  {
    return Op(Mult);
  }
  else if (msat_term_is_divide(env, term))
  {
    return Op(Div);
  }
  else if (msat_term_is_array_read(env, term))
  {
    return Op(Select);
  }
  else if (msat_term_is_array_write(env, term))
  {
    return Op(Store);
  }
  else if (msat_term_is_array_const(env, term))
  {
    // constant array is a value (has a null operator)
    return Op();
  }
  else if (msat_term_is_bv_concat(env, term))
  {
    return Op(Concat);
  }
  else if (msat_term_is_bv_or(env, term))
  {
    return Op(BVOr);
  }
  else if (msat_term_is_bv_xor(env, term))
  {
    return Op(BVXor);
  }
  else if (msat_term_is_bv_and(env, term))
  {
    return Op(BVAnd);
  }
  else if (msat_term_is_bv_not(env, term))
  {
    return Op(BVNot);
  }
  else if (msat_term_is_bv_plus(env, term))
  {
    return Op(BVAdd);
  }
  else if (msat_term_is_bv_minus(env, term))
  {
    return Op(BVSub);
  }
  else if (msat_term_is_bv_times(env, term))
  {
    return Op(BVMul);
  }
  else if (msat_term_is_bv_neg(env, term))
  {
    return Op(BVNeg);
  }
  else if (msat_term_is_bv_udiv(env, term))
  {
    return Op(BVUdiv);
  }
  else if (msat_term_is_bv_urem(env, term))
  {
    return Op(BVUrem);
  }
  else if (msat_term_is_bv_sdiv(env, term))
  {
    return Op(BVSdiv);
  }
  else if (msat_term_is_bv_srem(env, term))
  {
    return Op(BVSrem);
  }
  else if (msat_term_is_bv_ult(env, term))
  {
    return Op(BVUlt);
  }
  else if (msat_term_is_bv_uleq(env, term))
  {
    return Op(BVUle);
  }
  else if (msat_term_is_bv_slt(env, term))
  {
    return Op(BVSlt);
  }
  else if (msat_term_is_bv_sleq(env, term))
  {
    return Op(BVSle);
  }
  else if (msat_term_is_bv_lshl(env, term))
  {
    return Op(BVShl);
  }
  else if (msat_term_is_bv_lshr(env, term))
  {
    return Op(BVLshr);
  }
  else if (msat_term_is_bv_ashr(env, term))
  {
    return Op(BVAshr);
  }
  else if (msat_term_is_bv_comp(env, term))
  {
    return Op(BVComp);
  }
  else if (is_symbolic_const() || is_value())
  {
    return Op();
  }
  else
  {
    size_t idx0;
    size_t idx1;
    if (msat_term_is_bv_extract(env, term, &idx0, &idx1))
    {
      return Op(Extract, idx0, idx1);
    }
    else if (msat_term_is_bv_zext(env, term, &idx0))
    {
      return Op(Zero_Extend, idx0);
    }
    else if (msat_term_is_bv_sext(env, term, &idx0))
    {
      return Op(Sign_Extend, idx0);
    }
    else if (msat_term_is_bv_rol(env, term, &idx0))
    {
      return Op(Rotate_Left, idx0);
    }
    else if (msat_term_is_bv_ror(env, term, &idx0))
    {
      return Op(Rotate_Right, idx0);
    }
    else
    {
      char * s = msat_to_smtlib2_term(env, term);
      std::string msg("Msat term ");
      msg += s;
      msg += " has an unknown op.";
      msat_free(s);
      throw NotImplementedException(msg);
    }
  }
}

Sort MsatTerm::get_sort() const
{
  if (!is_uf)
  {
    return std::make_shared<MsatSort> (env, msat_term_get_type(term));
  }
  else
  {
    // need to reconstruct the function type
    vector<msat_type> param_types;
    size_t arity = msat_decl_get_arity(decl);
    param_types.reserve(arity);
    for (size_t i = 0; i < arity; i++)
    {
      param_types.push_back(msat_decl_get_arg_type(decl, i));
    }

    if (!param_types.size())
    {
      throw InternalSolverException("Expecting non-zero arity for UF.");
    }

    msat_type funtype = msat_get_function_type(env,
                                               &param_types[0],
                                               param_types.size(),
                                               msat_decl_get_return_type(decl));

    return std::make_shared<MsatSort> (env, funtype, decl);
  }
}

bool MsatTerm::is_symbolic_const() const
{
  // functions are currently considered symbols
  if (is_uf)
  {
    return true;
  }

  // a symbolic constant is a term with no children and no built-in
  // interpretation
  return (
      (msat_term_arity(term) == 0)
      && (msat_decl_get_tag(env, msat_term_get_decl(term)) == MSAT_TAG_UNKNOWN)
      && !msat_term_is_number(env, term));
}

bool MsatTerm::is_value() const
{
  if (is_uf)
  {
    return false;
  }

  // value if it has no children and a built-in interpretation
  return (msat_term_is_number(env, term) || msat_term_is_true(env, term)
          || msat_term_is_false(env, term) ||
          // constant arrays are considered values in smt-switch
          msat_term_is_array_const(env, term));
}

string MsatTerm::to_string()
{
  if (is_uf)
  {
    if (MSAT_ERROR_DECL(decl))
    {
      throw SmtException("Can't get representation for MathSAT error decl!");
    }
    string repr = msat_decl_repr(decl);
    size_t idx = repr.find(":");
    if (idx != string::npos)
    {
      repr = repr.substr(0, idx);
    }
    return repr;
  }
  else
  {
    if (MSAT_ERROR_TERM(term))
    {
      throw SmtException("Can't get representation for MathSAT error term!");
    }
    char * s = msat_to_smtlib2_term(env, term);
    string res = s;
    msat_free(s);
    return res;
  }
}

uint64_t MsatTerm::to_int() const
{
  char * s = msat_to_smtlib2_term(env, term);
  std::string val = s;
  msat_free(s);
  bool is_bv = msat_is_bv_type(env, msat_term_get_type(term), nullptr);

  // process smt-lib bit-vector format
  if (is_bv)
  {
    if (val.find("(_ bv") == std::string::npos)
    {
      std::string msg = val;
      msg += " is not a constant term, can't convert to int.";
      throw IncorrectUsageException(msg.c_str());
    }
    val = val.substr(5, val.length());
    val = val.substr(0, val.find(" "));
  }

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

TermIter MsatTerm::begin() { return TermIter(new MsatTermIter(env, term, 0)); }

TermIter MsatTerm::end()
{
  if (is_uf)
  {
    // term is null, but begin() and end() TermIter will evaluate as equal
    // which is what we want because function symbols have no children
    return TermIter(new MsatTermIter(env, term, 0));
  }

  uint32_t arity = msat_term_arity(term);
  if (msat_term_is_uf(env, term))
  {
    // consider the function itself a child
    arity++;
  }
  return TermIter(new MsatTermIter(env, term, arity));
}

// end MsatTerm implementation

}  // namespace smt
