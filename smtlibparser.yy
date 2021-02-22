%{
#include <cstdio>
#include <iostream>
using namespace std;
%}

%skeleton "lalr1.cc"
%require "3.7"
%defines

%define api.token.raw

%define api.token.constructor
%define api.value.type variant
%define parse.assert

%code requires {
  #include <string>
  #include "smt-switch/smt.h"

  class SmtLibDriver;
}

%param { SmtLibDriver & drv }

%locations

%define parse.trace
%define parse.error detailed
%define parse.lac full

%code {
#include "smtlib_driver.h"
}

%token <std::string> SYMBOL
%token NUMBER
%token SETLOGIC DECLARECONST ASSERT
%token <std::string> BOOL INT REAL
%token
LP "("
RP ")"

%nterm commands
%nterm command
%nterm smt2
%nterm s_expr
%nterm s_expr_list
%nterm atom
%nterm <smt::Sort> sort

%%

smt2:
  commands
  {
    cout << "Bison got commands in smt2 file" << endl;
  }
;

commands:
  %empty
  {}
  | commands command {}
;

command:
  LP SETLOGIC SYMBOL RP
  {
    cout << "Bison got a set-logic command with " << $3 << endl;
  }
  | LP DECLARECONST SYMBOL sort RP
  {
    smt::Term sym = drv.new_symbol($3, $4);
  }
  | LP ASSERT s_expr RP
  {
    cout << "Bison got an assert" << endl;
  }
;

s_expr:
  atom
  {
    cout << "Bison got an atom" << endl;
  }
  | LP s_expr_list RP
  {
    cout << "Bison got an s_expr list in parentheses" << endl;
  }
;

s_expr_list:
   s_expr
   {
     cout << "Got a single s-expression list" << endl;
   }
   | s_expr s_expr_list
   {
     cout << "Bison got an s-expression list" << endl;
   }
;

atom:
   SYMBOL
   {
     cout << "Bison got a symbol: " << $1 << endl;
   }
   | NUMBER
   {
     cout << "Bison got a number" << endl;
   }
;

sort:
   BOOL
   {
     $$ = drv.solver()->make_sort(smt::BOOL);
   }
   | INT
   {
     $$ = drv.solver()->make_sort(smt::INT);
   }
   | REAL
   {
     $$ = drv.solver()->make_sort(smt::REAL);
   }
;

%%

void yy::parser::error (const location_type& l, const std::string& m)
{
  cerr << l << ": " << m << endl;
}