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

  namespace smt
  {
    class SmtLibDriver;
  }
}

%param { smt::SmtLibDriver & drv }

%locations

%define parse.trace
%define parse.error detailed
%define parse.lac full

%code {
#include "smtlib_driver.h"
}

%token <std::string> SYMBOL
%token <std::string> INTEGER
%token SETLOGIC DECLARECONST DECLAREFUN ASSERT CHECKSAT
%token <std::string> BOOL INT REAL
%token <std::string> PRIMOP
%token
LP "("
RP ")"
INDPREFIX "(_"

%nterm commands
%nterm command
%nterm smt2
%nterm <smt::Term> s_expr
%nterm <smt::TermVec> s_expr_list
%nterm <smt::Term> atom
%nterm <smt::Sort> sort
%nterm <smt::SortVec> sort_list
%nterm <smt::Op> operator

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
    drv.new_symbol($3, $4);
  }
  | LP DECLAREFUN SYMBOL LP sort_list RP sort RP
  {
    smt::SortVec vec = $5;
    vec.push_back($7);
    smt::Sort funsort = drv.solver()->make_sort(smt::FUNCTION, vec);
    drv.new_symbol($3, funsort);
  }
  | LP ASSERT s_expr RP
  {
    cout << "Bison got assert for " << $3 << endl;
    drv.solver()->assert_formula($3);
  }
  | LP CHECKSAT RP
  {
    cout << drv.solver()->check_sat() << endl;
  }
;

s_expr:
  atom
  {
    cout << "Bison got an atom" << endl;
    $$ = $1;
  }
  | LP operator s_expr_list RP
  {
    cout << "Bison got an operator application using " << $2 << " with " << $3.size() << " args" << endl;
    $$ = drv.solver()->make_term($2, $3);
  }
  | LP s_expr_list RP
  {
    cout << "Bison got a UF application" << endl;
    $$ = drv.solver()->make_term(smt::Apply, $2);
  }
;

s_expr_list:
   s_expr
   {
     cout << "Got a single s-expression list" << endl;
     smt::TermVec vec({$1});
     $$ = vec;
   }
   | s_expr s_expr_list
   {
     cout << "Bison got an s-expression list" << endl;
     smt::TermVec vec({$1});
     vec.insert(vec.end(), $2.begin(), $2.end());
     $$ = vec;
   }
;

atom:
   SYMBOL
   {
     cout << "Bison got a symbol: " << $1 << endl;
     $$ = drv.lookup_symbol($1);
   }
   | INTEGER
   {
     cout << "Bison got a number" << endl;
     $$ = drv.solver()->make_term($1, drv.solver()->make_sort(smt::INT));
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

sort_list:
   sort
   {
     smt::SortVec vec({$1});
     $$ = vec;
   }
   | sort sort_list
   {
     smt::SortVec vec({$1});
     vec.insert(vec.end(), $2.begin(), $2.end());
     $$ = vec;
   }
;

operator:
   PRIMOP
   {
     $$ = drv.lookup_primop($1);
   }
;

%%

void yy::parser::error (const location_type& l, const std::string& m)
{
  cerr << l << ": " << m << endl;
}