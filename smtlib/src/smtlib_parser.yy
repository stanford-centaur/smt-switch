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
%define api.value.automove
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
%nterm <PrimOp> indexed_name
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

%start commands

%%

// These open and close a scope for the names an alternative binds, such as
// define-fun's arguments, around them and the body that uses them.
open_scope:
  %empty { drv.push_scope(); }
;

close_scope:
  %empty { drv.pop_scope(); }
;

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
| LP SETOPT attribute RP         { auto [k, v] = $3; drv.set_opt(k, v); }
| LP SETINFO attribute RP        { auto [k, v] = $3; drv.set_info(k, v); }
| LP DECLARECONST SYMBOL sort RP { drv.new_symbol($3, $4); }
| LP DECLAREFUN SYMBOL LP sort_list RP sort RP
  { drv.declare_fun($3, $5, $7); }
| LP DECLARESORT SYMBOL NAT RP   { drv.declare_sort($3, to_nat(@4, $4)); }
| LP DEFINEFUN open_scope SYMBOL LP sorted_arg_list RP sort term_s_expr
  close_scope RP                 { drv.define_fun($4, $9, $6); }
| LP DEFINESORT SYMBOL LP RP sort RP
  { drv.define_sort($3, $6); }
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
  { drv.get_value($4); }
| LP GETUNSATASSUMP RP           { drv.get_unsat_assumptions(); }
| LP ECHO stringlit RP           { drv.echo($3); }
;

term_s_expr:
  atom
| LP indexed_op term_s_expr_list RP { $$ = drv.solver()->make_term($2, $3); }
| LP SYMBOL term_s_expr_list RP     { $$ = drv.apply_symbol($2, $3); }
| LP LP ASCONST sort RP atom RP     { $$ = drv.solver()->make_term($6, $4); }
| LP QUANTIFIER LP open_scope sorted_param_list RP term_s_expr close_scope RP
  {
    TermVec params = $5;
    params.push_back($7);  // the body follows the parameters in smt-switch
    $$ = drv.solver()->make_term(drv.lookup_primop($2), params);
  }
| LP LET open_scope LP let_term_bindings RP term_s_expr close_scope RP
  { $$ = $7; }
| LP EP term_s_expr attributes RP
  {
    $$ = $3;
    for (const auto & attr : $4)
    {
      drv.term_attribute($$, attr.first, attr.second);
    }
  }
;

term_s_expr_list:
  %empty                       {}
| term_s_expr_list term_s_expr { $$ = $1; $$.push_back($2); }
;

atom:
  SYMBOL
  {
    const std::string & name = $1;
    $$ = drv.lookup_symbol(name);
    if (!$$)
    {
      throw syntax_error(@1, "Unrecognized symbol: " + name);
    }
  }
| FLOAT { $$ = drv.solver()->make_term($1, drv.solver()->make_sort(REAL)); }
| NAT   { $$ = drv.make_numeral($1); }
| bvconst
| QUOTESTRING
  { $$ = drv.solver()->make_term($1, false, drv.solver()->make_sort(STRING)); }
;

bvconst:
  BITSTR { $$ = drv.make_bv_value($1, 2); }
| HEXSTR { $$ = drv.make_bv_value($1, 16); }
| indprefix SYMBOL NAT RP
  {
    const std::string & name = $2;
    $$ = drv.make_bv_literal(name, to_nat(@3, $3));
    if (!$$)
    {
      throw syntax_error(@2, "Unknown indexed literal: " + name);
    }
  }
;

sort:
  SYMBOL { $$ = drv.make_sort($1); }
| indprefix SYMBOL NAT RP
  {
    const std::string & name = $2;
    $$ = drv.make_sort(name, to_nat(@3, $3));
    if (!$$)
    {
      throw syntax_error(@2, "Unrecognized sort: " + name);
    }
  }
| LP SYMBOL sort_list RP
  {
    $$ = drv.make_sort($2, $3);
    if (!$$)
    {
      throw syntax_error(@3, "Array takes an index and an element sort");
    }
  }
;

sort_list:
  %empty         {}
| sort_list sort { $$ = $1; $$.push_back($2); }
;

sorted_arg_list:
  %empty {}
| sorted_arg_list LP SYMBOL sort RP
  { $$ = $1; $$.push_back(drv.register_arg($3, $4)); }
;

sorted_param_list:
  %empty {}
| sorted_param_list LP SYMBOL sort RP
  { $$ = $1; $$.push_back(drv.create_param($3, $4)); }
;

let_term_bindings:
  %empty
| let_term_bindings LP SYMBOL term_s_expr RP { drv.let_binding($3, $4); }
;

indexed_op:
  indexed_name NAT RP     { $$ = Op($1, to_nat(@2, $2)); }
| indexed_name NAT NAT RP { $$ = Op($1, to_nat(@2, $2), to_nat(@3, $3)); }
;

indexed_name:
  indprefix SYMBOL
  {
    const std::string & name = $2;
    $$ = drv.lookup_primop(name);
    if ($$ == NUM_OPS_AND_NULL)
    {
      throw syntax_error(@2, "Unexpected symbol in indexed operator: " + name);
    }
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
    $$ = $1;
    if (!$$.empty())
    {
      $$ += ' ';
    }
    $$ += $2;
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
  %empty               {}
| attributes attribute { $$ = $1; $$.push_back($2); }
;
