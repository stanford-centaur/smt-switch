/*!
 * \file smtlib_parser.yy
 * \brief The SMT-LIB grammar, from which Bison generates the parser.
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
%skeleton "lalr1.cc"
%require "3.7"

// The location classes go in the parser's own header.
%define api.location.file none
%define api.namespace {smt}
%define api.parser.class {SmtLibParser}
%define api.prefix {smtlib}
%define api.token.raw
%define api.token.constructor
%define api.value.type variant
%define parse.error detailed
%define parse.lac full

%param { SmtLibScanner & scanner }
%parse-param { SmtLibReader & drv }

// Emitted into smtlib_parser.h, before the parser class.
%code requires {
#include <string>
#include <utility>

#include "ops.h"
#include "smt_defs.h"
#include "sort.h"
#include "term.h"

// SmtLibScanner is declared in smtlib_scanner.h, which includes this header.
namespace smt {
class SmtLibReader;
class SmtLibScanner;
}  // namespace smt
}

// Emitted into smtlib_parser.cpp only, after it includes the header.
%code {
#include <cstdint>
#include <iostream>
#include <stdexcept>

#include "smtlib_reader.h"
#include "smtlib_scanner.h"
#include "solver.h"

namespace smt {

static std::uint64_t to_nat(const SmtLibParser::location_type & l,
                            const std::string & s)
{
  try
  {
    return std::stoull(s);
  }
  catch (const std::out_of_range &)
  {
    throw SmtLibParser::syntax_error(l, "Numeral out of range: " + s);
  }
}

}  // namespace smt
}

%token <std::string> SYMBOL
%token <std::string> NAT
%token <std::string> FLOAT
%token <std::string> BITSTR
%token <std::string> HEXSTR
%token <std::string> QUOTESTRING
%token SETLOGIC SETOPT SETINFO DECLARECONST DECLAREFUN
       DECLARESORT DEFINEFUN DEFINESORT ASSERT CHECKSAT
       CHECKSATASSUMING PUSH POP EXIT GETVALUE
       GETUNSATASSUMP ECHO
%token ASCONST LET
%token <std::string> KEYWORD
%token <std::string> QUANTIFIER
%token
LP "("
RP ")"
US "_"
EP "!"

%nterm commands
%nterm command
%nterm smt2
%nterm <Term> term_s_expr
%nterm <TermVec> term_s_expr_list
%nterm <Term> atom
%nterm <Term> bvconst
%nterm <Sort> sort
%nterm <SortVec> sort_list
%nterm <TermVec> sorted_arg_list
%nterm <TermVec> sorted_param_list
%nterm let_term_bindings
%nterm <Op> indexed_op
%nterm <std::string> stringlit
%nterm <std::string> number
%nterm <std::string> number_or_string
%nterm indprefix

%nterm <std::string> spec_constant
%nterm <std::string> s_expr
%nterm <std::string> s_expr_list
%nterm <std::pair<std::string, std::string>> attribute
%nterm <std::vector<std::pair<std::string, std::string>>> attributes


%%

smt2:
  commands
  {}
;

commands:
  %empty
  {}
  | commands command
  {}
;

command:
  LP SETLOGIC SYMBOL RP
  {
    drv.set_logic($3);
  }
  | LP SETOPT attribute RP
  {
    auto attr = $3;
    drv.set_opt(attr.first, attr.second);
  }
  | LP SETINFO attribute RP
  {
    auto attr = $3;
    drv.set_info(attr.first, attr.second);
  }
  | LP DECLARECONST SYMBOL sort RP
  {
    drv.new_symbol($3, $4);
  }
  | LP DECLAREFUN SYMBOL LP sort_list RP sort RP
  {
    Sort symsort;
    if ($5.size())
    {
      SortVec & vec = $5;
      vec.push_back($7);
      symsort = drv.solver()->make_sort(FUNCTION, vec);
    }
    else
    {
      symsort = $7;
    }
    drv.new_symbol($3, symsort);
  }
  | LP DECLARESORT SYMBOL NAT RP
  {
    drv.define_sort($3, drv.solver()->make_sort($3, to_nat(@4, $4)));
  }
  | LP DEFINEFUN
    {
      // new scope for arguments
      drv.push_scope();
    }
    SYMBOL LP sorted_arg_list RP sort term_s_expr RP
  {
    drv.define_fun($4, $9, $6);

    drv.pop_scope();
  }
  | LP DEFINESORT SYMBOL LP RP sort RP
  {
    // only supports 0-arity define-sorts
    drv.define_sort($3, $6);
  }
  | LP ASSERT term_s_expr RP
  {
    drv.assert_formula($3);
  }
  | LP CHECKSAT RP
  {
    drv.check_sat();
  }
  | LP CHECKSATASSUMING LP term_s_expr_list RP RP
  {
    drv.check_sat_assuming($4);
  }
  | LP PUSH RP
  {
    drv.push();
  }
  | LP PUSH NAT RP
  {
    drv.push(to_nat(@3, $3));
  }
  | LP POP RP
  {
    drv.pop();
  }
  | LP POP NAT RP
  {
    drv.pop(to_nat(@3, $3));
  }
  | LP EXIT RP
  {
    YYACCEPT;
  }
  | LP GETVALUE LP term_s_expr_list RP RP
  {
    std::cout << "(";
    for (const auto & t : $4)
    {
      std::cout << "(" << t << " " << drv.solver()->get_value(t) << ") "
                << std::endl;
    }
    std::cout << ")" << std::endl;
  }
  | LP GETUNSATASSUMP RP
  {
    UnorderedTermSet core;
    drv.solver()->get_unsat_assumptions(core);
    std::cout << "(";
    for (const auto & c : core)
    {
      std::cout << c << std::endl;
    }
    std::cout << ")" << std::endl;
  }
  | LP ECHO stringlit RP
  {
    std::cout << $3 << std::endl;
  }
;

term_s_expr:
  atom
  {
    $$ = $1;
  }
  | LP indexed_op term_s_expr_list RP
  {
    $$ = drv.solver()->make_term($2, $3);
  }
  | LP SYMBOL term_s_expr_list RP
  {
    PrimOp po;
    Term uf;

    // check if it's a known operator in the given logic
    if ((po = drv.lookup_primop($2)) != NUM_OPS_AND_NULL)
    {
      // this is an operator
      $$ = drv.apply_primop(po, std::move($3));
    }
    else if ((uf = drv.lookup_symbol($2)))
    {
      TermVec vec({ uf });
      vec.insert(vec.end(), $3.begin(), $3.end());
      $$ = drv.solver()->make_term(Apply, vec);
    }
    else
    {
      // assuming this is a defined fun
      // will throw exception if not a defined function symbol
      $$ = drv.apply_define_fun($2, $3);
    }
  }
  | LP LP ASCONST sort RP atom RP
  {
    $$ = drv.solver()->make_term($6, $4);
  }
  | LP QUANTIFIER LP
    {
      // mid-rule for incrementing scope
      drv.push_scope();
    }
    sorted_param_list RP term_s_expr RP
  {
    PrimOp po = drv.lookup_primop($2);
    // smt-switch takes all the parameters followed by the body
    $5.push_back($7);
    $$ = drv.solver()->make_term(po, $5);

    // this scope is done
    drv.pop_scope();
  }
  | LP LET
    {
      // mid-rule for incrementing scope
      drv.push_scope();
    }
    LP let_term_bindings RP term_s_expr RP
  {
    drv.pop_scope();
    $$ = $7;
  }
  | LP EP term_s_expr attributes RP
  {
    // the default implementation does nothing
    // but print a warning to standard error.
    // it is possible to implement the function in derived class
    // to use the attribute
    for (const auto & attr : $4)
    {
      drv.term_attribute($3, attr.first, attr.second);
    }
    $$ = $3;
  }
;

term_s_expr_list:
  %empty
  {}
  | term_s_expr_list term_s_expr
  {
    $1.push_back($2);
    $$ = std::move($1);
  }
;

atom:
  SYMBOL
  {
    Term sym = drv.lookup_symbol($1);
    if (!sym)
    {
      // Note: using @1 will force locations to be enabled
      throw syntax_error(@1, "Unrecognized symbol: " + $1);
    }
    $$ = sym;
  }
  | FLOAT
  {
    $$ = drv.solver()->make_term($1, drv.solver()->make_sort(REAL));
  }
  | NAT
  {
    // in a logic of reals without integers, numerals are reals
    SortKind sk = drv.lookup_sortkind("Int") == NUM_SORT_KINDS
                               && drv.lookup_sortkind("Real") == REAL
                           ? REAL
                           : INT;
    $$ = drv.solver()->make_term($1, drv.solver()->make_sort(sk));
  }
  | bvconst
  {
    $$ = $1;
  }
  | QUOTESTRING
  {
    $$ = drv.solver()->make_term(
        $1, false, drv.solver()->make_sort(STRING));
  }
;

bvconst:
  BITSTR
  {
    Sort bvsort = drv.solver()->make_sort(BV, $1.length());
    $$ = drv.solver()->make_term($1, bvsort, 2);
  }
  | HEXSTR
  {
    Sort bvsort = drv.solver()->make_sort(BV, 4 * $1.length());
    $$ = drv.solver()->make_term($1, bvsort, 16);
  }
  | indprefix SYMBOL NAT RP
  {
    // bvN is a symbol like any other unless indexed, as in (_ bv5 8)
    const std::string & name = $2;
    if (name.size() < 3 || name.compare(0, 2, "bv") != 0
        || name.find_first_not_of("0123456789", 2) != std::string::npos)
    {
      throw syntax_error(@2, "Unknown indexed literal: " + name);
    }
    Sort bvsort = drv.solver()->make_sort(BV, to_nat(@3, $3));
    $$ = drv.solver()->make_term(name.substr(2), bvsort, 10);
  }
;

sort:
  SYMBOL
  {
    Sort res;
    // check built-in sort kinds first
    SortKind sk = drv.lookup_sortkind($1);
    if (sk == NUM_SORT_KINDS)
    {
      // got the dedicated null enum
      // check defined sorts
      res = drv.lookup_sort($1);
    }
    else if (sk == UNINTERPRETED)
    {
      // uninterpreted sorts also stored with defined sorts
      res = drv.lookup_sort($1);
    }
    else
    {
      res = drv.solver()->make_sort(sk);
    }
    $$ = res;
  }
  | indprefix SYMBOL NAT RP
  {
    // this one is intended for bit-vectors
    SortKind sk = drv.lookup_sortkind($2);
    if (sk == NUM_SORT_KINDS)
    {
      // got dedicated null enum
      throw syntax_error(@2, "Unrecognized sort: " + $2);
    }
    $$ = drv.solver()->make_sort(sk, to_nat(@3, $3));
  }
  | LP SYMBOL sort_list RP
  {
    SortKind sk = drv.lookup_sortkind($2);
    if (sk == ARRAY)
    {
      // this one is intended for arrays
      if ($3.size() != 2)
      {
        throw syntax_error(@3, "Array takes an index and an element sort");
      }
      $$ = drv.solver()->make_sort(sk, $3[0], $3[1]);
    }
    else
    {
      // defined or declared sort
      Sort sort_con = drv.lookup_sort($2);
      $$ = drv.solver()->make_sort(sort_con, $3);
    }
  }
;

sort_list:
  %empty
  {}
  | sort_list sort
  {
    $1.push_back($2);
    $$ = std::move($1);
  }
;

sorted_arg_list:
  %empty
  {}
  | sorted_arg_list LP SYMBOL sort RP
  {
    Term arg = drv.register_arg($3, $4);
    $1.push_back(arg);
    $$ = std::move($1);
  }
;

sorted_param_list:
  %empty
  {}
  | sorted_param_list LP SYMBOL sort RP
  {
    Term param = drv.create_param($3, $4);
    $1.push_back(param);
    $$ = std::move($1);
  }
;

let_term_bindings:
  %empty
  {}
  | let_term_bindings LP SYMBOL term_s_expr RP
  {
    drv.let_binding($3, $4);
  }
;

indexed_op:
  indprefix SYMBOL NAT RP
  {
    PrimOp po = drv.lookup_primop($2);
    if (po == NUM_OPS_AND_NULL)
    {
      throw syntax_error(@2, "Unexpected symbol in indexed operator: " + $2);
    }
    $$ = Op(po, to_nat(@3, $3));
  }
  | indprefix SYMBOL NAT NAT RP
  {
    PrimOp po = drv.lookup_primop($2);
    if (po == NUM_OPS_AND_NULL)
    {
      throw syntax_error(@2, "Unexpected symbol in indexed operator: " + $2);
    }
    $$ = Op(po, to_nat(@3, $3), to_nat(@4, $4));
  }
;

stringlit:
  QUOTESTRING
  {
    $$ = $1;
  }
  | SYMBOL
  {
    $$ = $1;
  }
;

number:
  NAT
  {
    $$ = $1;
  }
  | FLOAT
  {
    $$ = $1;
  }
;

number_or_string:
  number
  {
    $$ = $1;
  }
  | stringlit
  {
    $$ = $1;
  }
;

indprefix:
  LP US
  {}
;

spec_constant:
  number_or_string
  {
    $$ = $1;
  }
  | BITSTR
  {
    $$ = $1;
  }
  | HEXSTR
  {
    $$ = $1;
  }
;

s_expr:
  spec_constant
  {
    $$ = $1;
  }
  | LP s_expr_list RP
  {
    $$ = "(" + $2 + ")";
  }
;

s_expr_list:
  %empty
  {
    $$ = "";
  }
  | s_expr_list s_expr
  {
    $1 += $2;
    $$ = $1;
  }
;

attribute:
  KEYWORD
  {
    $$ = { $1, "" };
  }
  | KEYWORD s_expr
  {
    $$ = { $1, $2 };
  }
;

attributes:
  %empty
  {}
  | attributes attribute
  {
    $1.push_back(std::move($2));
    $$ = std::move($1);
  }
;

%%

namespace smt {

void SmtLibParser::error(const location_type & l, const std::string & m)
{
  throw syntax_error(l, m);
}

}  // namespace smt
