#ifndef SMT_PRIM_OPS_H
#define SMT_PRIM_OPS_H

#include "uf.h"

#include <array>
#include <string>

namespace smt {
// Primitive SMT operations (and identifiers for building indexed operators)
// TODO add more smt ops
enum PrimOp {
  AND = 0,
  OR,
  XOR,
  NOT,
  IMPLIES,
  IFF,
  ITE,
  EQUAL,
  BVAND,
  BVOR,
  BVXOR,
  BVNOT,
  BVNEG,
  BVADD,
  BVSUB,
  BVMUL,
  BVUREM,
  BVSREM,
  BVMOD,
  BVASHR,
  BVLSHR,
  BVSHL,
  BVULT,
  BVULE,
  BVUGT,
  BVUGE,
  BVSLT,
  BVSLE,
  BVSGT,
  BVSGE,
  EXTRACT,
  ZERO_EXTEND,
  SIGN_EXTEND,
  SELECT,
  STORE,
  // distinguish between const and variable in the leaves
  // TODO: Decide if it should be Value/Const instead
  CONST,
  VAR,
  /**
     Serves as both the number of ops and a null element for builtin operators.
   */
  NUM_OPS_AND_NULL
};

/**
   This function should only be called once, to generate the constexpr
   primop2str for converting enums to string_views.
*/
constexpr std::array<std::string_view, NUM_OPS_AND_NULL> generate_primop2str() {
  std::array<std::string_view, NUM_OPS_AND_NULL> primop2str;

  primop2str[AND] = std::string_view("AND");
  primop2str[OR] = std::string_view("OR");
  primop2str[XOR] = std::string_view("XOR");
  primop2str[NOT] = std::string_view("NOT");
  primop2str[IMPLIES] = std::string_view("IMPLIES");
  primop2str[IFF] = std::string_view("IFF");
  primop2str[ITE] = std::string_view("ITE");
  primop2str[EQUAL] = std::string_view("EQUAL");
  primop2str[BVAND] = std::string_view("BVAND");
  primop2str[BVOR] = std::string_view("BVOR");
  primop2str[BVXOR] = std::string_view("BVXOR");
  primop2str[BVNOT] = std::string_view("BVNOT");
  primop2str[BVNEG] = std::string_view("BVNEG");
  primop2str[BVADD] = std::string_view("BVADD");
  primop2str[BVSUB] = std::string_view("BVSUB");
  primop2str[BVMUL] = std::string_view("BVMUL");
  primop2str[BVUREM] = std::string_view("BVUREM");
  primop2str[BVSREM] = std::string_view("BVSREM");
  primop2str[BVMOD] = std::string_view("BVMOD");
  primop2str[BVASHR] = std::string_view("BVASHR");
  primop2str[BVLSHR] = std::string_view("BVLSHR");
  primop2str[BVSHL] = std::string_view("BVSHL");
  primop2str[BVULT] = std::string_view("BVULT");
  primop2str[BVULE] = std::string_view("BVULE");
  primop2str[BVUGT] = std::string_view("BVUGT");
  primop2str[BVUGE] = std::string_view("BVUGE");
  primop2str[BVSLT] = std::string_view("BVSLT");
  primop2str[BVSLE] = std::string_view("BVSLE");
  primop2str[BVSGT] = std::string_view("BVSGT");
  primop2str[BVSGE] = std::string_view("BVSGE");
  primop2str[EXTRACT] = std::string_view("EXTRACT");
  primop2str[SELECT] = std::string_view("SELECT");
  primop2str[STORE] = std::string_view("STORE");
  primop2str[CONST] = std::string_view("CONST");
  primop2str[VAR] = std::string_view("VAR");

  return primop2str;
}

constexpr std::array<std::string_view, NUM_OPS_AND_NULL> primop2str =
    generate_primop2str();

std::string_view to_string(PrimOp op)
{
  return primop2str[op];
}

} // namespace smt

#endif
