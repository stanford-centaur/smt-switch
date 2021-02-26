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
  #include "smt.h"

  namespace smt
  {
    class SmtLibReader;
  }
}

%param { smt::SmtLibReader & drv }

%locations

%define parse.trace
%define parse.error detailed
%define parse.lac full

%code {
#include "smtlib_reader.h"
}

%token <std::string> SYMBOL
%token <std::string> NAT
%token <std::string> FLOAT
%token <std::string> BITSTR
%token <std::string> HEXSTR
%token <std::string> BVDEC
%token <std::string> QUOTESTRING
%token SETLOGIC SETOPT SETINFO DECLARECONST DECLAREFUN
       DEFINEFUN ASSERT CHECKSAT CHECKSATASSUMING PUSH
       POP EXIT
%token BOOL INT REAL BITVEC ARRAY
%token ASCONST
%token <std::string> KEYWORD
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
%nterm <smt::Term> bvconst
%nterm <smt::Sort> sort
%nterm <smt::SortVec> sort_list
%nterm <smt::TermVec> sorted_arg_list
%nterm <smt::Op> operator
%nterm <std::string> stringlit
%nterm <std::string> number
%nterm <std::string> number_or_string

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
    drv.set_logic($4);

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP SETOPT
     {
       // mid-action rule to set current command
       drv.set_command(smt::SETOPT);
     }
    KEYWORD SYMBOL RP
  {
    drv.set_opt($4, $5);

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP SETINFO
    {
       // mid-action rule to set current command
       drv.set_command(smt::SETINFO);
    }
    KEYWORD number_or_string RP
    {
      drv.set_info($4, $5);

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
    smt::Sort symsort;
    if ($6.size())
    {
      smt::SortVec & vec = $6;
      vec.push_back($8);
      symsort = drv.solver()->make_sort(smt::FUNCTION, vec);
    }
    else
    {
      symsort = $8;
    }
    assert(symsort);
    drv.new_symbol($4, symsort);

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
    NAT RP
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
    NAT RP
  {
    drv.pop(std::stoi($4));

    // unset command now that it's done
    drv.set_command(smt::NONE);
  }
  | LP EXIT RP
  {
    YYACCEPT;
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
    // TODO clean up this bison rule -- need to allow a define-fun
    //      or a UF. Currently define-fun has no term representation
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
  | LP LP ASCONST sort RP atom RP
  {
    $$ = drv.solver()->make_term($6, $4);
  }
;

s_expr_list:
   %empty
   {
     smt::TermVec vec;
     $$ = vec;
   }
   | s_expr_list s_expr
   {
     smt::TermVec & vec = $1;
     vec.push_back($2);
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
   | NAT
   {
     $$ = drv.solver()->make_term($1, drv.solver()->make_sort(smt::INT));
   }
   | bvconst
   {
     $$ = $1;
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
     smt::Sort bvsort = drv.solver()->make_sort(smt::BV, 4*($1.length()));
     $$ = drv.solver()->make_term($1, bvsort, 16);
   }
   | INDPREFIX BVDEC NAT RP
   {
     smt::Sort bvsort = drv.solver()->make_sort(smt::BV, std::stoi($3));
     $$ = drv.solver()->make_term($2, bvsort, 10);
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
   | INDPREFIX BITVEC NAT RP
   {
     $$ = drv.solver()->make_sort(smt::BV, std::stoi($3));
   }
   | LP ARRAY sort sort RP
   {
     $$ = drv.solver()->make_sort(smt::ARRAY, $3, $4);
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
     smt::TermVec vec;
     $$ = vec;
   }
   | sorted_arg_list LP SYMBOL sort RP
   {
     smt::Term arg = drv.register_arg($3, $4);
     smt::TermVec & vec = $1;
     vec.push_back(arg);
     $$ = vec;
   }
;

operator:
   PRIMOP
   {
     $$ = drv.lookup_primop($1);
   }
   | INDPREFIX PRIMOP NAT RP
   {
     $$ = smt::Op(drv.lookup_primop($2), std::stoi($3));
   }
   | INDPREFIX PRIMOP NAT NAT RP
   {
     $$ = smt::Op(drv.lookup_primop($2), std::stoi($3), std::stoi($4));
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


%%

void yy::parser::error (const location_type& l, const std::string& m)
{
  cerr << l << ": " << m << endl;
}