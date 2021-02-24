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
%token SETLOGIC SETOPT DECLARECONST DECLAREFUN DEFINEFUN
       ASSERT CHECKSAT CHECKSATASSUMING PUSH POP
%token <std::string> OPT
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
%nterm <smt::TermVec> sorted_arg_list
%nterm <smt::Op> operator

%%

smt2:
  commands
  {}
;

commands:
  %empty
  {}
  | commands command {}
;

command:
  LP SETLOGIC
     {
       // mid-action rule to set current command
       drv.set_command(smt::SETLOGIC);
     }
  SYMBOL RP
  {
    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP SETOPT
     {
       // mid-action rule to set current command
       drv.set_command(smt::SETOPT);
     }
    OPT SYMBOL RP
  {
    drv.solver()->set_opt($4, $5);

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP DECLARECONST
     {
       // mid-action rule to set current command
       drv.set_command(smt::DECLARECONST);
     }
    SYMBOL sort RP
  {
    drv.new_symbol($4, $5);

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP DECLAREFUN
     {
       // mid-action rule to set current command
       drv.set_command(smt::DECLAREFUN);
     }
    SYMBOL LP sort_list RP sort RP
  {
    smt::SortVec vec = $6;
    vec.push_back($8);
    smt::Sort funsort = drv.solver()->make_sort(smt::FUNCTION, vec);
    drv.new_symbol($4, funsort);

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP DEFINEFUN
     {
       // mid-action rule to set current command
       drv.set_command(smt::DEFINEFUN);
     }
    SYMBOL LP sorted_arg_list RP s_expr RP
  {
    drv.define_fun($4, $8, $6);

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP ASSERT
     {
       // mid-action rule to set current command
       drv.set_command(smt::ASSERT);
     }
    s_expr RP
  {
    drv.assert_formula($4);

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP CHECKSAT
     {
       // mid-action rule to set current command
       drv.set_command(smt::CHECKSAT);
     }
    RP
  {
    drv.check_sat();

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP CHECKSATASSUMING
     {
       // mid-action rule to set current command
       drv.set_command(smt::CHECKSATASSUMING);
     }
    LP s_expr_list RP RP
  {
    drv.check_sat_assuming($5);

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP PUSH
     {
       // mid-action rule to set current command
       drv.set_command(smt::PUSH);
     }
    RP
  {
    drv.push();

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP PUSH
     {
       // mid-action rule to set current command
       drv.set_command(smt::PUSH);
     }
    INTEGER RP
  {
    drv.push(std::stoi($4));

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP POP
     {
       // mid-action rule to set current command
       drv.set_command(smt::POP);
     }
    RP
  {
    drv.pop();

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP POP
     {
       // mid-action rule to set current command
       drv.set_command(smt::POP);
     }
    INTEGER RP
  {
    drv.pop(std::stoi($4));

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
;

s_expr:
  atom
  {
    $$ = $1;
  }
  | LP operator s_expr_list RP
  {
    $$ = drv.solver()->make_term($2, $3);
  }
  | LP SYMBOL s_expr_list RP
  {
    // will return a null term if symbol doesn't exist
    smt::Term uf = drv.lookup_symbol($2);
    if (uf)
    {
      smt::TermVec vec({uf});
      vec.insert(vec.end(), $3.begin(), $3.end());
      $$ = drv.solver()->make_term(smt::Apply, vec);
    }
    else
    {
      // assuming this is a defined fun
      // TODO better error message
      $$ = drv.apply_define_fun($2, $3);
    }
  }
;

s_expr_list:
   s_expr
   {
     smt::TermVec vec({$1});
     $$ = vec;
   }
   | s_expr s_expr_list
   {
     smt::TermVec vec({$1});
     vec.insert(vec.end(), $2.begin(), $2.end());
     $$ = vec;
   }
;

atom:
   SYMBOL
   {
     if (drv.current_command() == smt::DEFINEFUN)
     {
       // could be a temporary argument
       $$ = drv.lookup_arg($1);
     }
     else
     {
       smt::Term sym = drv.lookup_symbol($1);
       if (!sym)
       {
         yy::parser::error(@1, std::string("Unrecognized symbol: ") + $1);
         YYERROR;
       }
       $$ = sym;
     }
   }
   | INTEGER
   {
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

sorted_arg_list:
   LP SYMBOL sort RP
   {
     smt::Term arg = drv.register_arg($2, $3);
     smt::TermVec vec({arg});
     $$ = vec;
   }
   | LP SYMBOL sort RP sorted_arg_list
   {
     smt::Term arg = drv.register_arg($2, $3);
     smt::TermVec vec({arg});
     vec.insert(vec.end(), $5.begin(), $5.end());
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