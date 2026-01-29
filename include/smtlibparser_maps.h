#include <string>
#include <unordered_map>

#include "ops.h"

namespace smt {

// maps theories to operators
// based on strings used in SMT-LIB logics
const std::unordered_map<std::string, std::unordered_map<std::string, PrimOp>>
    strict_theory2opmap(
        { { "Core",
            {
                { "and", And },
                { "or", Or },
                { "xor", Xor },
                { "not", Not },
                { "=>", Implies },
                { "ite", Ite },
                { "=", Equal },
                { "distinct", Distinct },
                { "forall", Forall },
                { "exists", Exists },
            } },
          // Uninterpreted Functions
          { "UF",
            // empty map, don't want to reserve the symbol "apply"
            {} },
          // Integers
          { "IA",
            { { "+", Plus },
              { "-", Minus },
              // Need to pick which one based on context
              // { "-", Negate },
              { "<", Lt },
              { "<=", Le },
              { ">", Gt },
              { ">=", Ge },
              { "*", Mult },
              { "div", IntDiv },
              { "mod", Mod },
              { "abs", Abs } } },
          // Reals
          { "RA",
            {
                { "+", Plus },
                { "-", Minus },
                // Need to pick which one based on context
                // { "-", Negate },
                { "<", Lt },
                { "<=", Le },
                { ">", Gt },
                { ">=", Ge },
                { "*", Mult },
                { "/", Div },
            } },
          { "IRA",
            {
                { "to_real", To_Real },
                { "to_int", To_Int },
                { "is_int", Is_Int },
            } },
          // FixedSizeBitVectors
          { "BV",
            { { "concat", Concat },
              { "extract", Extract },
              { "bvnot", BVNot },
              { "bvneg", BVNeg },
              { "bvand", BVAnd },
              { "bvor", BVOr },
              { "bvxor", BVXor },
              { "bvnand", BVNand },
              { "bvnor", BVNor },
              { "bvxnor", BVXnor },
              { "bvcomp", BVComp },
              { "bvadd", BVAdd },
              { "bvsub", BVSub },
              { "bvmul", BVMul },
              { "bvudiv", BVUdiv },
              { "bvsdiv", BVSdiv },
              { "bvurem", BVUrem },
              { "bvsrem", BVSrem },
              { "bvsmod", BVSmod },
              { "bvshl", BVShl },
              { "bvashr", BVAshr },
              { "bvlshr", BVLshr },
              { "bvult", BVUlt },
              { "bvule", BVUle },
              { "bvugt", BVUgt },
              { "bvuge", BVUge },
              { "bvslt", BVSlt },
              { "bvsle", BVSle },
              { "bvsgt", BVSgt },
              { "bvsge", BVSge },
              { "zero_extend", Zero_Extend },
              { "sign_extend", Sign_Extend },
              { "repeat", Repeat },
              { "rotate_left", Rotate_Left },
              { "rotate_right", Rotate_Right } } },
          // Strings
          { "S",
            {
                { "str.<", StrLt },
                { "str.<=", StrLeq },
                { "str.len", StrLen },
                { "str.++", StrConcat },
                { "str.substr", StrSubstr },
                { "str.at", StrAt },
                { "str.contains", StrContains },
                { "str.indexof", StrIndexof },
                { "str.replace", StrReplace },
                { "str.replace_all", StrReplaceAll },
                { "str.prefixof", StrPrefixof },
                { "str.suffixof", StrSuffixof },
                { "str.is_digit", StrIsDigit },
            } },
          // ArraysEx
          { "A",
            {
                { "select", Select },
                { "store", Store },
            } } });

const std::unordered_map<std::string, std::unordered_map<std::string, PrimOp>>
    nonstrict_theory2opmap({ { "BVIA",
                               {
                                   { "int2bv", Int_To_BV },
                                   { "int_to_bv", Int_To_BV },
                                   { "bv2nat", UBV_To_Int },
                                   { "ubv_to_int", UBV_To_Int },
                                   { "sbv_to_int", SBV_To_Int },
                               } },
                             { "IA", { { "pow", Pow } } } });

}  // namespace smt
