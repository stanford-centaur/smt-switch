/*!
 * \file z3_term.cpp
 * \brief Z3 implementation of AbsTerm
 * \author Lindsey Stuntz
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/z3_term.h"

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/solver_utils.h"
#include "smt-switch/text_utils.h"
#include "smt-switch/z3_sort.h"

namespace smt {

namespace {

// Whether a Z3 expression is a literal, an abstract value, a constant array,
// a constructor applied to values or a store of values
bool is_z3_value(const z3::expr & term)
{
  if (term.is_true() || term.is_false() || term.is_numeral())
  {
    return true;
  }
  else if (!term.is_app())
  {
    return false;
  }
  Z3_decl_kind kind = term.decl().decl_kind();
  // SMT-LIB's ArraysEx makes a store of a value into an array value a value
  if (kind == Z3_OP_DT_CONSTRUCTOR || kind == Z3_OP_STORE)
  {
    for (unsigned i = 0; i < term.num_args(); ++i)
    {
      if (!is_z3_value(term.arg(i)))
      {
        return false;
      }
    }
    return true;
  }
  return kind == Z3_OP_CONST_ARRAY
         || (kind == Z3_OP_UNINTERPRETED && term.is_const()
             && term.decl().num_parameters() != 0);
}

}  // namespace

// Z3Term implementation

Z3Term::Z3Term(const std::shared_ptr<Z3Context> & c, z3::expr t)
    : ctx(c), term(t), z_func(*c)
{
}

Z3Term::Z3Term(const std::shared_ptr<Z3Context> & c, z3::func_decl zfunc)
    : ctx(c), term(*c), z_func(zfunc), is_function(true)
{
}

size_t Z3Term::hash() const
{
  if (!is_function)
  {
    return term.hash();
  }
  else
  {
    return z_func.hash();
  }
}

std::size_t Z3Term::get_id() const
{
  if (!is_function)
  {
    return term.id();
  }
  else
  {
    return z_func.id();
  }
}

bool Z3Term::compare(const Term & absterm) const
{
  std::shared_ptr<Z3Term> zs = std::dynamic_pointer_cast<Z3Term>(absterm);
  if (!zs)
  {
    return false;
  }
  if (is_function && zs->is_function)
  {
    return z3::eq(z_func, zs->z_func);
  }
  else if (!is_function && !zs->is_function)
  {
    return z3::eq(term, zs->term);
  }
  return false;
}

Op Z3Term::get_op() const
{
  // a nullary constructor is a constant that applies it
  if (is_function
      || (term.is_const() && term.decl().decl_kind() != Z3_OP_DT_CONSTRUCTOR))
  {
    return Op();
  }
  else if (term.is_lambda())
  {
    // Z3 gives one as the model value of an array it cannot write as stores
    throw NotImplementedException("Z3 lambda terms have no smt-switch op: "
                                  + term.to_string());
  }
  else if (term.is_quantifier())
  {
    return term.is_forall() ? Op(Op::Forall) : Op(Op::Exists);
  }
  else if (!term.is_app())
  {
    return Op();
  }
  else if (ctx->is_int_power(term))
  {
    return Op(Op::Pow);
  }
  else
  {
    z3::func_decl decl = term.decl();
    Z3_decl_kind kind = decl.decl_kind();

    switch (kind)
    {
      // unary
      case Z3_OP_NOT: return Op(Op::Not);
      case Z3_OP_UMINUS: return Op(Op::Negate);
      case Z3_OP_TO_REAL: return Op(Op::To_Real);
      case Z3_OP_TO_INT: return Op(Op::To_Int);
      case Z3_OP_IS_INT: return Op(Op::Is_Int);
      case Z3_OP_BNOT: return Op(Op::BVNot);
      case Z3_OP_BNEG:
        return Op(Op::BVNeg);
        // binary
      case Z3_OP_XOR: return Op(Op::Xor);
      case Z3_OP_IMPLIES: return Op(Op::Implies);
      case Z3_OP_POWER: return Op(Op::Pow);
      case Z3_OP_IDIV: return Op(Op::IntDiv);
      case Z3_OP_DIV: return Op(Op::Div);
      case Z3_OP_LT: return Op(Op::Lt);
      case Z3_OP_LE: return Op(Op::Le);
      case Z3_OP_GT: return Op(Op::Gt);
      case Z3_OP_GE: return Op(Op::Ge);
      case Z3_OP_EQ: return Op(Op::Equal);
      case Z3_OP_MOD: return Op(Op::Mod);
      case Z3_OP_CONCAT: return Op(Op::Concat);
      case Z3_OP_BAND: return Op(Op::BVAnd);
      case Z3_OP_BOR: return Op(Op::BVOr);
      case Z3_OP_BXOR: return Op(Op::BVXor);
      case Z3_OP_BNAND: return Op(Op::BVNand);
      case Z3_OP_BNOR: return Op(Op::BVNor);
      case Z3_OP_BXNOR: return Op(Op::BVXnor);
      case Z3_OP_BADD: return Op(Op::BVAdd);
      case Z3_OP_BSUB: return Op(Op::BVSub);
      case Z3_OP_BMUL: return Op(Op::BVMul);
      case Z3_OP_BUDIV: return Op(Op::BVUdiv);
      case Z3_OP_BUREM: return Op(Op::BVUrem);
      case Z3_OP_BSDIV: return Op(Op::BVSdiv);
      case Z3_OP_BSREM: return Op(Op::BVSrem);
      case Z3_OP_BSMOD: return Op(Op::BVSmod);
      case Z3_OP_BSHL: return Op(Op::BVShl);
      case Z3_OP_BASHR: return Op(Op::BVAshr);
      case Z3_OP_BLSHR: return Op(Op::BVLshr);
      case Z3_OP_ULT: return Op(Op::BVUlt);
      case Z3_OP_ULEQ: return Op(Op::BVUle);
      case Z3_OP_UGT: return Op(Op::BVUgt);
      case Z3_OP_UGEQ: return Op(Op::BVUge);
      case Z3_OP_SLEQ: return Op(Op::BVSle);
      case Z3_OP_SLT: return Op(Op::BVSlt);
      case Z3_OP_SGEQ: return Op(Op::BVSge);
      case Z3_OP_SGT: return Op(Op::BVSgt);
      case Z3_OP_SELECT:
        return Op(Op::Select);
        // ternary
      case Z3_OP_ITE: return Op(Op::Ite);
      case Z3_OP_STORE: return Op(Op::Store);
      case Z3_OP_CONST_ARRAY:
        return Op();
        // variadic
      case Z3_OP_AND: return Op(Op::And);
      case Z3_OP_OR: return Op(Op::Or);
      case Z3_OP_ADD: return Op(Op::Plus);
      case Z3_OP_SUB: return Op(Op::Minus);
      case Z3_OP_MUL: return Op(Op::Mult);
      case Z3_OP_DISTINCT:
        return Op(Op::Distinct);
        // indexed
      case Z3_OP_EXTRACT: {
        return Op(Op::Extract,
                  Z3_get_decl_int_parameter(term.ctx(), decl, 0),
                  Z3_get_decl_int_parameter(term.ctx(), decl, 1));
      }
      case Z3_OP_ZERO_EXT: {
        return Op(Op::Zero_Extend,
                  Z3_get_decl_int_parameter(term.ctx(), decl, 0));
      }
      case Z3_OP_SIGN_EXT: {
        return Op(Op::Sign_Extend,
                  Z3_get_decl_int_parameter(term.ctx(), decl, 0));
      }
      case Z3_OP_REPEAT: {
        return Op(Op::Repeat, Z3_get_decl_int_parameter(term.ctx(), decl, 0));
      }
      case Z3_OP_ROTATE_LEFT:
        return Op(Op::Rotate_Left,
                  Z3_get_decl_int_parameter(term.ctx(), decl, 0));
      case Z3_OP_ROTATE_RIGHT:
        return Op(Op::Rotate_Right,
                  Z3_get_decl_int_parameter(term.ctx(), decl, 0));
      case Z3_OP_INT2BV: {
        size_t out_width = decl.range().bv_size();
        return Op(Op::Int_To_BV, out_width);
      }
      case Z3_OP_BV2INT: return Op(Op::UBV_To_Int);
#ifdef SMT_SWITCH_Z3_HAS_SBV2INT
      case Z3_OP_SBV2INT: return Op(Op::SBV_To_Int);
#endif
      case Z3_OP_UNINTERPRETED: return Op(Op::Apply);
      case Z3_OP_DT_CONSTRUCTOR: return Op(Op::Apply_Constructor);
      case Z3_OP_DT_ACCESSOR: return Op(Op::Apply_Selector);
      case Z3_OP_DT_IS: return Op(Op::Apply_Tester);
      // Z3 makes divisibility an internal op, which only its name tells apart
      case Z3_OP_INTERNAL:
        if (decl.name().str() == "divisible"
            && Z3_get_decl_num_parameters(term.ctx(), decl) == 1)
        {
          return Op(Op::Divisible,
                    Z3_get_decl_int_parameter(term.ctx(), decl, 0));
        }
        [[fallthrough]];
      default:
        throw NotImplementedException(
            "smt-switch has no operator for the Z3 operator "
            + decl.name().str());
    }
  }
}

Sort Z3Term::get_sort() const
{
  if (!is_function)
  {
    return std::make_shared<Z3Sort>(ctx, term.get_sort());
  }
  return std::make_shared<Z3Sort>(ctx, z_func);
}

bool Z3Term::is_symbol() const
{
  // a function is an uninterpreted one or a datatype constructor, selector
  // or tester, which its datatype declares, not make_symbol
  if (is_function)
  {
    return z_func.decl_kind() == Z3_OP_UNINTERPRETED;
  }
  return term.is_const() && !is_value()
         && term.decl().decl_kind() != Z3_OP_DT_CONSTRUCTOR;
}

bool Z3Term::is_param() const { return !is_function && ctx->is_param(term); }

bool Z3Term::is_symbolic_const() const
{
  if (is_function || is_param())
  {
    return false;
  }
  return is_symbol();
}

bool Z3Term::is_value() const { return !is_function && is_z3_value(term); }

std::string Z3Term::to_string() const
{
  if (is_function)
  {
    // Z3 names every tester `is`, so a tester is printed with the
    // constructor it tests
    if (z_func.decl_kind() == Z3_OP_DT_IS)
    {
      return "(_ is " + smtlib::quote_symbol(get_constructor_name()) + ")";
    }
    return smtlib::quote_symbol(z_func.name().str());
  }
  else
  {
    return ctx->print_term(term);
  }
}

std::string Z3Term::get_constructor_name() const
{
  if (is_function && z_func.decl_kind() == Z3_OP_DT_CONSTRUCTOR)
  {
    return z_func.name().str();
  }
  // Z3 names every tester `is`, so a tester's constructor is read from its
  // parameter
  if (is_function && z_func.decl_kind() == Z3_OP_DT_IS)
  {
    z3::func_decl cons{ *ctx,
                        Z3_get_decl_func_decl_parameter(*ctx, z_func, 0) };
    return cons.name().str();
  }
  throw IncorrectUsageException(
      "Only a constructor or a tester has a constructor name");
}

std::string Z3Term::get_param_name() const
{
  if (!is_param())
  {
    throw IncorrectUsageException("Only a param has a param name");
  }
  return ctx->get_param_name(term);
}

std::string Z3Term::get_selector_name() const
{
  if (is_function && z_func.decl_kind() == Z3_OP_DT_ACCESSOR)
  {
    return z_func.name().str();
  }
  throw IncorrectUsageException("Only a selector has a selector name");
}

std::string Z3Term::get_symbol_name() const
{
  if (!is_symbol() || is_param())
  {
    throw IncorrectUsageException(
        "Only a symbol that is not a param has a symbol name");
  }
  const z3::symbol name = (is_function ? z_func : term.decl()).name();
  // Z3 makes an empty name its null symbol, whose text is <null>.
  if (Z3_symbol(name) == Z3_symbol(name.ctx().str_symbol("")))
  {
    return "";
  }
  return name.str();
}

uint64_t Z3Term::to_int() const
{
  if (!is_function && term.is_numeral())
  {
    if (term.is_bv())
    {
      return bits_to_uint64(to_bits());
    }
    // succeeds for integer values and for real values with an integral
    // value, if they fit
    uint64_t res;
    if (term.is_arith() && term.is_numeral_u64(res))
    {
      return res;
    }
  }
  throw IncorrectUsageException(
      "Can't convert " + (is_function ? z_func.name().str() : term.to_string())
      + " to an unsigned integer: it is not a value that fits in 64 bits");
}

int64_t Z3Term::to_signed_int() const
{
  if (!is_function && term.is_numeral())
  {
    if (term.is_bv())
    {
      return bits_to_int64(to_bits());
    }
    // succeeds for integer values and for real values with an integral
    // value, if they fit
    int64_t res;
    if (term.is_arith() && term.is_numeral_i64(res))
    {
      return res;
    }
  }
  throw IncorrectUsageException(
      "Can't convert " + (is_function ? z_func.name().str() : term.to_string())
      + " to a signed integer: it is not a value that fits in 64 bits");
}

std::string Z3Term::to_bits() const
{
  if (is_function || !term.is_numeral() || !term.is_bv())
  {
    throw IncorrectUsageException(
        "Can't get a bitstring from a term that is not a bit-vector value");
  }
  // without leading zeros
  const std::string bits = Z3_get_numeral_binary_string(term.ctx(), term);
  return std::string(term.get_sort().bv_size() - bits.size(), '0') + bits;
}

bool Z3Term::to_bool() const
{
  if (!is_function)
  {
    if (term.is_true())
    {
      return true;
    }
    if (term.is_false())
    {
      return false;
    }
  }
  throw IncorrectUsageException(
      "Can't convert " + (is_function ? z_func.name().str() : term.to_string())
      + " to a Boolean: it is not a Boolean value");
}

// The children smt-switch lists, with the function, constructor, selector or
// tester applied first. Only a function's term is null, and it has no
// children. The cast asks whether the term is null, as z3::expr's operator!
// makes a negation.
std::size_t Z3Term::get_num_children() const
{
  if (!static_cast<bool>(term))
  {
    return 0;
  }

  const Op::Kind kind = get_op().kind();
  if (kind == Op::Forall || kind == Op::Exists || kind == Op::Pow)
  {
    return 2;
  }
  std::size_t num_args = term.num_args();
  return is_apply(kind) ? num_args + 1 : num_args;
}

Term Z3Term::get_child(std::size_t i) const
{
  // the index as Z3 takes an argument index
  const unsigned pos = backend::narrow<unsigned>(i, "a child position");
  const Op::Kind kind = get_op().kind();
  // smt-switch lists the first bound variable and then the body, which
  // binds the rest; Z3 binds them all in one quantifier, as de Bruijn
  // indices, and keeps their names
  if (kind == Op::Forall || kind == Op::Exists)
  {
    if (pos > 1)
    {
      throw IncorrectUsageException("A quantifier has only two children");
    }
    const unsigned num_bound = Z3_get_quantifier_num_bound(*ctx, term);
    // a bound variable's name and sort make the param it was made from
    z3::expr_vector bound(*ctx);
    for (unsigned k = 0; k < num_bound; ++k)
    {
      bound.push_back(
          z3::expr(*ctx,
                   Z3_mk_const(*ctx,
                               Z3_get_quantifier_bound_name(*ctx, term, k),
                               Z3_get_quantifier_bound_sort(*ctx, term, k))));
    }
    if (pos == 0)
    {
      return std::make_shared<Z3Term>(ctx, bound[0]);
    }
    // index 0 is the last bound variable
    std::vector<Z3_ast> by_index(num_bound);
    for (unsigned k = 0; k < num_bound; ++k)
    {
      by_index[k] = bound[num_bound - 1 - k];
    }
    z3::expr body(*ctx,
                  Z3_substitute_vars(*ctx,
                                     Z3_get_quantifier_body(*ctx, term),
                                     num_bound,
                                     by_index.data()));
    ctx->check_error();
    if (num_bound == 1)
    {
      return std::make_shared<Z3Term>(ctx, body);
    }
    z3::expr_vector rest(*ctx);
    for (unsigned k = 1; k < num_bound; ++k)
    {
      rest.push_back(bound[k]);
    }
    return std::make_shared<Z3Term>(
        ctx,
        term.is_forall() ? z3::forall(rest, body) : z3::exists(rest, body));
  }
  // the base and exponent of the power Z3Context::make_int_power makes
  if (pos < 2 && kind == Op::Pow && term.decl().decl_kind() == Z3_OP_ITE)
  {
    return std::make_shared<Z3Term>(
        ctx, pos == 0 ? term.arg(2).arg(0).arg(0) : term.arg(0).arg(0));
  }
  // smt-switch lists the function, constructor, selector or tester applied
  // as the first child, which Z3 keeps as the decl
  if (is_apply(kind))
  {
    return pos == 0 ? std::make_shared<Z3Term>(ctx, term.decl())
                    : std::make_shared<Z3Term>(ctx, term.arg(pos - 1));
  }
  return std::make_shared<Z3Term>(ctx, term.arg(pos));
}

std::string Z3Term::print_value_as(SortKind /* sk */) const
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Can't use print_value_as on a term that is not a value");
  }
  return term.to_string();
}

z3::expr Z3Term::get_z3_expr() const
{
  if (is_function)
  {
    throw IncorrectUsageException(
        "Can't get a Z3 expression from a function term");
  }
  return term;
}

z3::func_decl Z3Term::get_z3_func_decl() const
{
  if (!is_function)
  {
    throw IncorrectUsageException(
        "Can't get a Z3 function from a term that is not a function");
  }
  return z_func;
}

// end Z3Term implementation

}  // namespace smt
