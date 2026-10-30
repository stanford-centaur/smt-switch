/*!
 * \file smtlibparser.yy
 * \brief The SMT-LIB grammar, from which Bison generates the parser.
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
%skeleton "lalr1.cc"
%require "3.7"

// The location classes go in the parser's own header.
%define api.location.file none
%define api.prefix {smtlib}
%define api.token.raw
%define api.token.constructor
%define api.value.type variant

%param { yyscan_t scanner }
%parse-param { smt::SmtLibReader & drv }

// Emitted into smtlibparser.h, before the parser class.
%code requires {
#include <string>
#include <utility>

#include "ops.h"
#include "smt_defs.h"
#include "sort.h"
#include "term.h"

namespace smt {
class SmtLibReader;
}  // namespace smt

// The scanner's state, defined as in flex's smtlibscanner.h, which cannot be
// included here: the scanner includes this header and repeats that one.
#ifndef YY_TYPEDEF_YY_SCANNER_T
#define YY_TYPEDEF_YY_SCANNER_T
typedef void * yyscan_t;
#endif
}

// Emitted into smtlibparser.h, after the parser class.
%code provides {
// The scanner's yylex, renamed by the prefix, returning the parser's tokens.
// smtlibscanner.h declares an int yylex unless this is defined first.
#define YY_DECL smtlib::parser::symbol_type smtliblex(yyscan_t yyscanner)
YY_DECL;
}

// Emitted into smtlibparser.cpp only, after it includes the header.
%code {
#include <cassert>
#include <iostream>

#include "smtlib_reader.h"
#include "solver.h"
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
%nterm <smt::Term> term_s_expr
%nterm <smt::TermVec *> term_s_expr_list
%nterm <smt::Term> atom
%nterm <smt::Term> bvconst
%nterm <smt::Sort> sort
%nterm <smt::SortVec> sort_list
%nterm <smt::TermVec *> sorted_arg_list
%nterm <smt::TermVec *> sorted_param_list
%nterm let_term_bindings
%nterm <smt::Op> indexed_op
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
    smt::Sort symsort;
    if ($5.size())
    {
      smt::SortVec & vec = $5;
      vec.push_back($7);
      symsort = drv.solver()->make_sort(smt::FUNCTION, vec);
    }
    else
    {
      symsort = $7;
    }
    assert(symsort);
    drv.new_symbol($3, symsort);
  }
  | LP DECLARESORT SYMBOL NAT RP
  {
    drv.define_sort($3, drv.solver()->make_sort($3, std::stoi($4)));
  }
  | LP DEFINEFUN
    {
      // new scope for arguments
      drv.push_scope();
    }
    SYMBOL LP sorted_arg_list RP sort term_s_expr RP
  {
    drv.define_fun($4, $9, *$6);

    drv.pop_scope();
    assert(!drv.current_scope());
    delete $6;
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
    drv.check_sat_assuming(*$4);
    delete $4;
  }
  | LP PUSH RP
  {
    drv.push();
  }
  | LP PUSH NAT RP
  {
    drv.push(std::stoi($3));
  }
  | LP POP RP
  {
    drv.pop();
  }
  | LP POP NAT RP
  {
    drv.pop(std::stoi($3));
  }
  | LP EXIT RP
  {
    YYACCEPT;
  }
  | LP GETVALUE LP term_s_expr_list RP RP
  {
    std::cout << "(";
    for (const auto & t : *$4)
    {
      std::cout << "(" << t << " " << drv.solver()->get_value(t) << ") "
                << std::endl;
    }
    std::cout << ")" << std::endl;
    delete $4;
  }
  | LP GETUNSATASSUMP RP
  {
    smt::UnorderedTermSet core;
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
    $$ = drv.solver()->make_term($2, *$3);
    delete $3;
  }
  | LP SYMBOL term_s_expr_list RP
  {
    smt::PrimOp po;
    smt::Term uf;

    // check if it's a known operator in the given logic
    if ((po = drv.lookup_primop($2)) != smt::NUM_OPS_AND_NULL)
    {
      // this is an operator
      $$ = drv.apply_primop(po, *$3);
    }
    else if ((uf = drv.lookup_symbol($2)))
    {
      smt::TermVec vec({ uf });
      vec.insert(vec.end(), $3->begin(), $3->end());
      $$ = drv.solver()->make_term(smt::Apply, vec);
    }
    else
    {
      // assuming this is a defined fun
      // will throw exception if not a defined function symbol
      $$ = drv.apply_define_fun($2, *$3);
    }
    delete $3;
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
    smt::PrimOp po = drv.lookup_primop($2);
    // smt-switch takes all the parameters followed by the body
    $5->push_back($7);
    $$ = drv.solver()->make_term(po, *$5);

    // this scope is done
    drv.pop_scope();
    delete $5;
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
  {
    $$ = new smt::TermVec();
  }
  | term_s_expr_list term_s_expr
  {
    $1->push_back($2);
    $$ = $1;
  }
;

atom:
  SYMBOL
  {
    smt::Term sym = drv.lookup_symbol($1);
    if (!sym)
    {
      // Note: using @1 will force locations to be enabled
      smtlib::parser::error(@1, std::string("Unrecognized symbol: ") + $1);
      YYERROR;
    }
    $$ = sym;
  }
  | FLOAT
  {
    $$ = drv.solver()->make_term($1, drv.solver()->make_sort(smt::REAL));
  }
  | NAT
  {
    // in a logic of reals without integers, numerals are reals
    smt::SortKind sk = drv.lookup_sortkind("Int") == smt::NUM_SORT_KINDS
                               && drv.lookup_sortkind("Real") == smt::REAL
                           ? smt::REAL
                           : smt::INT;
    $$ = drv.solver()->make_term($1, drv.solver()->make_sort(sk));
  }
  | bvconst
  {
    $$ = $1;
  }
  | QUOTESTRING
  {
    $$ = drv.solver()->make_term(
        $1, false, drv.solver()->make_sort(smt::STRING));
  }
;

bvconst:
  BITSTR
  {
    smt::Sort bvsort = drv.solver()->make_sort(smt::BV, $1.length());
    $$ = drv.solver()->make_term($1, bvsort, 2);
  }
  | HEXSTR
  {
    smt::Sort bvsort = drv.solver()->make_sort(smt::BV, 4 * $1.length());
    $$ = drv.solver()->make_term($1, bvsort, 16);
  }
  | indprefix SYMBOL NAT RP
  {
    // bvN is a symbol like any other unless indexed, as in (_ bv5 8)
    const std::string & name = $2;
    if (name.size() < 3 || name.compare(0, 2, "bv") != 0
        || name.find_first_not_of("0123456789", 2) != std::string::npos)
    {
      smtlib::parser::error(@2, "Unknown indexed literal: " + name);
      YYERROR;
    }
    smt::Sort bvsort = drv.solver()->make_sort(smt::BV, std::stoi($3));
    $$ = drv.solver()->make_term(name.substr(2), bvsort, 10);
  }
;

sort:
  SYMBOL
  {
    smt::Sort res;
    // check built-in sort kinds first
    smt::SortKind sk = drv.lookup_sortkind($1);
    if (sk == smt::NUM_SORT_KINDS)
    {
      // got the dedicated null enum
      // check defined sorts
      res = drv.lookup_sort($1);
    }
    else if (sk == smt::UNINTERPRETED)
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
    smt::SortKind sk = drv.lookup_sortkind($2);
    if (sk == smt::NUM_SORT_KINDS)
    {
      // got dedicated null enum
      smtlib::parser::error(@2, std::string("Unrecognized sort: ") + $2);
      YYERROR;
    }
    $$ = drv.solver()->make_sort(sk, std::stoi($3));
  }
  | LP SYMBOL sort_list RP
  {
    smt::SortKind sk = drv.lookup_sortkind($2);
    if (sk == smt::ARRAY)
    {
      // this one is intended for arrays
      $$ = drv.solver()->make_sort(sk, $3[0], $3[1]);
    }
    else
    {
      // defined or declared sort
      smt::Sort sort_con = drv.lookup_sort($2);
      $$ = drv.solver()->make_sort(sort_con, $3);
    }
  }
;

sort_list:
  %empty
  {
    smt::SortVec vec;
    $$ = vec;
  }
  | sort_list sort
  {
    smt::SortVec & vec = $1;
    vec.push_back($2);
    $$ = vec;
  }
;

sorted_arg_list:
  %empty
  {
    $$ = new smt::TermVec();
  }
  | sorted_arg_list LP SYMBOL sort RP
  {
    assert(drv.current_scope());
    smt::Term arg = drv.register_arg($3, $4);
    $1->push_back(arg);
    $$ = $1;
  }
;

sorted_param_list:
  %empty
  {
    $$ = new smt::TermVec();
  }
  | sorted_param_list LP SYMBOL sort RP
  {
    assert(drv.current_scope());
    smt::Term param = drv.create_param($3, $4);
    $1->push_back(param);
    $$ = $1;
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
    smt::PrimOp po = drv.lookup_primop($2);
    if (po == smt::NUM_OPS_AND_NULL)
    {
      smtlib::parser::error(@2, "Unexpected symbol in indexed operator: " + $2);
      YYERROR;
    }
    $$ = smt::Op(po, std::stoi($3));
  }
  | indprefix SYMBOL NAT NAT RP
  {
    smt::PrimOp po = drv.lookup_primop($2);
    if (po == smt::NUM_OPS_AND_NULL)
    {
      smtlib::parser::error(@2, "Unexpected symbol in indexed operator: " + $2);
      YYERROR;
    }
    $$ = smt::Op(po, std::stoi($3), std::stoi($4));
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
  {
    $$ = {};
  }
  | attributes attribute
  {
    $1.push_back($2);
    $$ = $1;
  }
;

%%

void smtlib::parser::error(const location_type & l, const std::string & m)
{
  std::cerr << l << ": " << m << std::endl;
}
