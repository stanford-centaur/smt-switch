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
%token SETLOGIC
%token
LP "("
RP ")"

%nterm s_expr
%nterm s_expr_list
%nterm atom

%%

s_expr:
  atom
  {
    cout << "Bison got an atom" << endl;
  }
  | LP SETLOGIC SYMBOL RP
  {
    cout << "Bison got a set-logic command with " << $3 << endl;
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

%%

void yy::parser::error (const location_type& l, const std::string& m)
{
  cerr << l << ": " << m << endl;
}