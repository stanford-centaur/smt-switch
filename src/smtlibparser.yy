%{
/*********************                                                        */
/*! \file smtlibparser.[yy/cpp]
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bison file and auto-generated parser.
**
**
**/

#include <cstdio>
#include <iostream>
using namespace std;
%}

%skeleton "lalr1.cc"
%require "3.7"

%define api.token.raw
%define api.value.automove
%define api.token.constructor
%define api.value.type variant

%code requires {
/*********************                                                        */
/*! \file smtlibparser.[yy/h]
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bison file and auto-generated parser.
**
**
**/
  #include <string>
  #include "smt.h"

  namespace smt
  {
    class SmtLibReader;
  }
}

%param { smt::SmtLibReader & drv }

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
       DEFINEFUN DEFINESORT ASSERT CHECKSAT
       CHECKSATASSUMING PUSH POP EXIT GETVALUELP
       GETUNSATASSUMP ECHO
%token BOOL INT REAL BITVEC ARRAY
%token ASCONST LET
%token <std::string> KEYWORD
%token <std::string> PRIMOP
%token <std::string> QUANTIFIER
%token
LP "("
RP ")"
US "_"

%nterm commands
%nterm command
%nterm smt2
%nterm <smt::Term> s_expr
%nterm <smt::TermVec *> s_expr_list
%nterm <smt::Term> atom
%nterm <smt::Term> bvconst
%nterm <smt::Sort> sort
%nterm <smt::SortVec> sort_list
%nterm <smt::TermVec *> sorted_arg_list
%nterm <smt::TermVec *> sorted_param_list
%nterm let_term_bindings
%nterm <smt::Op> operator
%nterm <std::string> stringlit
%nterm <std::string> number
%nterm <std::string> number_or_string
%nterm indprefix

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
  LP SETLOGIC SYMBOL RP
  {
    drv.set_logic($3);
  }
  | LP SETOPT KEYWORD SYMBOL RP
  {
    drv.set_opt($3, $4);
  }
  | LP SETINFO KEYWORD number_or_string RP
  {
    drv.set_info($3, $4);
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
  | LP DEFINEFUN
     {
       // new scope for arguments
       drv.push_scope();
     }
    SYMBOL LP sorted_arg_list RP sort s_expr RP
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
  | LP ASSERT s_expr RP
  {
    drv.assert_formula($3);
  }
  | LP CHECKSAT RP
  {
    drv.check_sat();
  }
  | LP CHECKSATASSUMING LP s_expr_list RP RP
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
  | LP GETVALUELP s_expr_list RP  RP
  {
    cout << "(";
    for (const auto & t : *$3)
    {
      cout << "(" << t << " " << drv.solver()->get_value(t) << ") " << endl;
    }
    cout << ")" << endl;
    delete $3;
  }
  | LP GETUNSATASSUMP RP
  {
    smt::UnorderedTermSet core;
    drv.solver()->get_unsat_assumptions(core);
    cout << "(";
    for (const auto & c : core)
    {
      cout << c << endl;
    }
    cout << ")" << endl;
  }
  | LP ECHO stringlit RP
  {
    cout << $3 << endl;
  }
;

s_expr:
  atom
  {
    $$ = $1;
  }
  | LP operator s_expr_list RP
  {
    // special-case for MINUS
    // needs to be negate if only one argument
    // TODO: might be a more elegant way to handle this
    if ($2 == smt::Minus && $3->size() == 1)
    {
      $$ = drv.solver()->make_term(smt::Negate, $3->at(0));
    }
    else
    {
      $$ = drv.solver()->make_term($2, *$3);
    }
    delete $3;
  }
  | LP SYMBOL s_expr_list RP
  {
    // will return a null term if symbol doesn't exist
    smt::Term uf = drv.lookup_symbol($2);
    if (uf)
    {
      smt::TermVec vec({uf});
      vec.insert(vec.end(), $3->begin(), $3->end());
      $$ = drv.solver()->make_term(smt::Apply, vec);
    }
    else
    {
      // assuming this is a defined fun
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
    sorted_param_list RP s_expr RP
  {
    smt::SmtSolver & solver = drv.solver();
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
    LP let_term_bindings RP s_expr RP
  {
    drv.pop_scope();
    $$ = $7;
  }
;

s_expr_list:
   %empty
   {
     $$ = new smt::TermVec();
   }
   | s_expr_list s_expr
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
        yy::parser::error(@1, std::string("Unrecognized symbol: ") + $1);
        YYERROR;
      }
      $$ = sym;
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
   | indprefix BVDEC NAT RP
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
   | indprefix BITVEC NAT RP
   {
     $$ = drv.solver()->make_sort(smt::BV, std::stoi($3));
   }
   | LP ARRAY sort sort RP
   {
     $$ = drv.solver()->make_sort(smt::ARRAY, $3, $4);
   }
   | SYMBOL
   {
     $$ = drv.lookup_sort($1);
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
   | let_term_bindings LP SYMBOL s_expr RP
   {
     drv.let_binding($3, $4);
   }


operator:
   PRIMOP
   {
     $$ = drv.lookup_primop($1);
   }
   | indprefix PRIMOP NAT RP
   {
     $$ = smt::Op(drv.lookup_primop($2), std::stoi($3));
   }
   | indprefix PRIMOP NAT NAT RP
   {
     $$ = smt::Op(drv.lookup_primop($2), std::stoi($3), std::stoi($4));
   }
;

stringlit:
   QUOTESTRING
   {
     $$ = $1;
   }
   | stringlit QUOTESTRING
   {
     $$ = $1 + $2;
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


%%

void yy::parser::error (const location_type& l, const std::string& m)
{
  cerr << l << ": " << m << endl;
}
