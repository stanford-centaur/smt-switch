/*!
 * \file smtlib_parser.yy
 * \brief The SMT-LIB grammar, from which Bison generates the parser.
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
%require "3.7"
%skeleton "lalr1.cc"

// The location classes go in the parser's own header.
%define api.location.file none
%define api.namespace {smt}
%define api.parser.class {SmtLibParser}
%define api.prefix {smtlib}
%define api.token.constructor
%define api.token.raw
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
#include "utils.h"

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

void SmtLibParser::error(const location_type & l, const std::string & m)
{
  throw syntax_error(l, m);
}

}  // namespace smt
}

// Symbols and keywords, with their text
%token <std::string> SYMBOL KEYWORD

// Literals, with their text
%token <std::string> NAT FLOAT BITSTR HEXSTR QUOTESTRING

// Command names, with their text
%token <std::string> SETLOGIC SETOPT SETINFO
%token <std::string> DECLARECONST DECLAREFUN DECLARESORT DEFINEFUN DEFINESORT
%token <std::string> ASSERT CHECKSAT CHECKSATASSUMING PUSH POP EXIT
%token <std::string> GETVALUE GETUNSATASSUMP ECHO

// Reserved words of terms, with their text: forall/exists, as const, and let
%token <std::string> QUANTIFIER ASCONST LET

// Punctuation, where _ and ! are reserved words, with their text
%token LP "("
%token RP ")"
%token <std::string> US "_"
%token <std::string> EP "!"

// The types of the nonterminals' values; the other nonterminals have none
%nterm <Term> term_s_expr
%nterm <TermVec> term_s_expr_list
%nterm <Term> atom
%nterm <Term> bvconst
%nterm <Sort> sort
%nterm <SortVec> sort_list
%nterm <TermVec> sorted_arg_list
%nterm <TermVec> sorted_param_list
%nterm <Op> indexed_op
%nterm <std::string> stringlit
%nterm <std::string> number
%nterm <std::string> number_or_string
%nterm <std::string> bv_literal
%nterm <std::string> spec_constant
%nterm <std::string> s_expr
%nterm <std::string> s_expr_list
%nterm <std::string> nested_s_expr
%nterm <std::string> reserved_word
%nterm <std::pair<std::string, std::string>> attribute
%nterm <std::vector<std::pair<std::string, std::string>>> attributes

%%

// An alternative without an action gives its rule the value of its first
// symbol, as $$ = $1, or no value if the rule has none. An empty
// alternative of a rule with a value has the action {}, which keeps the
// default value of the rule's type, such as an empty vector or string.

commands:
  %empty
| commands command
;

command:
  LP SETLOGIC SYMBOL RP          { drv.set_logic($3); }
| LP SETOPT attribute RP         { drv.set_opt($3.first, $3.second); }
| LP SETINFO attribute RP        { drv.set_info($3.first, $3.second); }
| LP DECLARECONST SYMBOL sort RP { drv.new_symbol($3, $4); }
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
  { drv.define_sort($3, drv.solver()->make_sort($3, to_nat(@4, $4))); }
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
| LP ASSERT term_s_expr RP       { drv.assert_formula($3); }
| LP CHECKSAT RP                 { drv.check_sat(); }
| LP CHECKSATASSUMING LP term_s_expr_list RP RP
  { drv.check_sat_assuming($4); }
| LP PUSH RP                     { drv.push(); }
| LP PUSH NAT RP                 { drv.push(to_nat(@3, $3)); }
| LP POP RP                      { drv.pop(); }
| LP POP NAT RP                  { drv.pop(to_nat(@3, $3)); }
| LP EXIT RP                     { YYACCEPT; }
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
| LP ECHO stringlit RP           { std::cout << $3 << std::endl; }
;

term_s_expr:
  atom
| LP indexed_op term_s_expr_list RP { $$ = drv.solver()->make_term($2, $3); }
| LP SYMBOL term_s_expr_list RP
  {
    PrimOp po;
    Term uf;

    // check if it's a known operator in the given logic
    if ((po = drv.lookup_primop($2)) != NUM_OPS_AND_NULL)
    {
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
      $$ = drv.apply_define_fun($2, $3);
    }
  }
| LP LP ASCONST sort RP atom RP     { $$ = drv.solver()->make_term($6, $4); }
| LP QUANTIFIER LP
  {
    // new scope for the parameters
    drv.push_scope();
  }
  sorted_param_list RP term_s_expr RP
  {
    PrimOp po = drv.lookup_primop($2);
    // smt-switch takes all the parameters followed by the body
    $5.push_back($7);
    $$ = drv.solver()->make_term(po, $5);
    drv.pop_scope();
  }
| LP LET
  {
    // new scope for the bindings
    drv.push_scope();
  }
  LP let_term_bindings RP term_s_expr RP
  {
    drv.pop_scope();
    $$ = $7;
  }
| LP EP term_s_expr attributes RP
  {
    for (const auto & attr : $4)
    {
      drv.term_attribute($3, attr.first, attr.second);
    }
    $$ = $3;
  }
;

term_s_expr_list:
  %empty {}
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
      throw syntax_error(@1, "Unrecognized symbol: " + $1);
    }
    $$ = sym;
  }
| FLOAT { $$ = drv.solver()->make_term($1, drv.solver()->make_sort(REAL)); }
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
| QUOTESTRING
  { $$ = drv.solver()->make_term($1, false, drv.solver()->make_sort(STRING)); }
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
    SortKind sk = drv.lookup_sortkind($1);
    if (sk == NUM_SORT_KINDS || sk == UNINTERPRETED)
    {
      $$ = drv.lookup_sort($1);
    }
    else
    {
      $$ = drv.solver()->make_sort(sk);
    }
  }
| indprefix SYMBOL NAT RP
  {
    SortKind sk = drv.lookup_sortkind($2);
    if (sk == NUM_SORT_KINDS)
    {
      throw syntax_error(@2, "Unrecognized sort: " + $2);
    }
    $$ = drv.solver()->make_sort(sk, to_nat(@3, $3));
  }
| LP SYMBOL sort_list RP
  {
    SortKind sk = drv.lookup_sortkind($2);
    if (sk == ARRAY)
    {
      if ($3.size() != 2)
      {
        throw syntax_error(@3, "Array takes an index and an element sort");
      }
      $$ = drv.solver()->make_sort(sk, $3[0], $3[1]);
    }
    else
    {
      Sort sort_con = drv.lookup_sort($2);
      $$ = drv.solver()->make_sort(sort_con, $3);
    }
  }
;

sort_list:
  %empty {}
| sort_list sort
  {
    $1.push_back($2);
    $$ = std::move($1);
  }
;

sorted_arg_list:
  %empty {}
| sorted_arg_list LP SYMBOL sort RP
  {
    $1.push_back(drv.register_arg($3, $4));
    $$ = std::move($1);
  }
;

sorted_param_list:
  %empty {}
| sorted_param_list LP SYMBOL sort RP
  {
    $1.push_back(drv.create_param($3, $4));
    $$ = std::move($1);
  }
;

let_term_bindings:
  %empty
| let_term_bindings LP SYMBOL term_s_expr RP { drv.let_binding($3, $4); }
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
| SYMBOL
;

number:
  NAT
| FLOAT
;

number_or_string:
  number
| stringlit
;

indprefix:
  LP US
;

bv_literal:
  BITSTR { $$ = "#b" + $1; }
| HEXSTR { $$ = "#x" + $1; }
;

spec_constant:
  number_or_string
| bv_literal
;

// An attribute's value, where a string or symbol stands for its text
s_expr:
  spec_constant
| LP s_expr_list RP { $$ = "(" + $2 + ")"; }
;

s_expr_list:
  %empty {}
| s_expr_list nested_s_expr
  {
    if (!$1.empty())
    {
      $1 += ' ';
    }
    $1 += $2;
    $$ = std::move($1);
  }
;

// An element of a list, as SMT-LIB writes it
nested_s_expr:
  number
| bv_literal
| QUOTESTRING       { $$ = '"' + $1 + '"'; }
| SYMBOL            { $$ = smtlib_quote_symbol($1); }
| KEYWORD           { $$ = ':' + $1; }
| reserved_word
| LP s_expr_list RP { $$ = "(" + $2 + ")"; }
;

reserved_word:
  US
| EP
| SETLOGIC
| SETOPT
| SETINFO
| DECLARECONST
| DECLAREFUN
| DECLARESORT
| DEFINEFUN
| DEFINESORT
| ASSERT
| CHECKSAT
| CHECKSATASSUMING
| PUSH
| POP
| EXIT
| GETVALUE
| GETUNSATASSUMP
| ECHO
| QUANTIFIER
| ASCONST
| LET
;

attribute:
  KEYWORD        { $$ = { $1, "" }; }
| KEYWORD s_expr { $$ = { $1, $2 }; }
;

attributes:
  %empty {}
| attributes attribute
  {
    $1.push_back(std::move($2));
    $$ = std::move($1);
  }
;
