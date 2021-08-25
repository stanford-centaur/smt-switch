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

%define api.token.constructor
%define api.value.type variant

%define api.prefix {smtlib}

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
  #include <utility>
  #include "smt.h"

  namespace smt
  {
    class SmtLibReader;

    // used as semantic values for datatypes declarations in parser
    using SelectorDecVec = std::vector<std::pair<std::string, smt::Sort>>;
    using ConstructorDecVec = std::vector<std::pair<std::string,
                                                    SelectorDecVec>>;

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
       DECLARESORT DECLAREDATATYPE DECLAREDATATYPES DEFINEFUN
       DEFINESORT ASSERT CHECKSAT CHECKSATASSUMING PUSH POP
       EXIT GETVALUE GETUNSATASSUMP ECHO
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
%nterm <std::pair<std::string, std::size_t>> sort_dec
%nterm <std::vector<std::pair<std::string, std::size_t>>> sort_decs
%nterm <smt::TermVec *> sorted_arg_list
%nterm <smt::TermVec *> sorted_param_list
%nterm let_term_bindings
/* The Term will be null if it's just a regular indexed op */
%nterm <std::pair<smt::Op, smt::Term>> indexed_op
%nterm <std::string> stringlit
%nterm <std::string> number
%nterm <std::string> number_or_string
%nterm indprefix
%nterm <std::pair<smt::DatatypeDecl, smt::Sort>> datatypesym
%nterm <std::vector<std::pair<smt::DatatypeDecl, smt::Sort>>> datatypesorts
%nterm <std::vector<smt::ConstructorDecVec>> datatypedecs
%nterm <smt::ConstructorDecVec> cons_list
%nterm <smt::SelectorDecVec> sel_list

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
  | commands command {}
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
  | LP DECLAREDATATYPE datatypesym LP cons_list RP RP
  {
    smt::SmtSolver & solver = drv.solver();
    smt::DatatypeDecl dtspec = $3.first;
    smt::Sort fwd_ref = $3.second;
    assert(dtspec); assert(fwd_ref);
    drv.declare_datatype(dtspec, fwd_ref, $5);
  }
  | LP DECLAREDATATYPES datatypesorts LP datatypedecs RP RP
  {
    size_t num_sorts = $3.size();
    size_t num_decs  = $5.size();
    if (num_sorts != num_decs)
    {
      smtlib::parser::error(@1, std::string("Declare datatypes needs "
      "same number of sort and datatype declarations but got " +
      std::to_string(num_sorts) + " and " + std::to_string(num_decs)));
      YYERROR;
    }

    smt::SmtSolver & solver = drv.solver();
    for (size_t i = 0; i < num_sorts; i++)
    {
      smt::DatatypeDecl dtspec = $3[i].first;
      smt::Sort fwd_ref = $3[i].second;
      assert(dtspec); assert(fwd_ref);
      drv.declare_datatype(dtspec, fwd_ref, $5[i]);
    }
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
  | LP GETVALUE LP term_s_expr_list RP  RP
  {
    cout << "(";
    for (const auto & t : *$4)
    {
      cout << "(" << t << " " << drv.solver()->get_value(t) << ") " << endl;
    }
    cout << ")" << endl;
    delete $4;
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

term_s_expr:
  atom
  {
    $$ = $1;
  }
  | LP indexed_op term_s_expr_list RP
  {
    std::pair<smt::Op, smt::Term> & opterm = $2;
    if (opterm.second)
    {
      // non-null term means this is an
      // APPLY* indexed operator
      // example: datatype tester like (_ is cons)
      smt::TermVec vec({opterm.second});
      vec.insert(vec.end(), $3->begin(), $3->end());
      $$ = drv.solver()->make_term(opterm.first, vec);
    }
    else
    {
      $$ = drv.solver()->make_term(opterm.first, *$3);
    }
    delete $3;
  }
  | LP SYMBOL term_s_expr_list RP
  {
    smt::PrimOp po;
    smt::Term apply_term; // UF, or datatype constructor/selector

    // check if it's a known operator in the given logic
    if ((po = drv.lookup_primop($2)) != smt::NUM_OPS_AND_NULL)
    {
       // this is an operator
       // special-case for MINUS
       // needs to be negate if only one argument
       // TODO: might be a more elegant way to handle this
       if (po == smt::Minus && $3->size() == 1)
       {
         $$ = drv.solver()->make_term(smt::Negate, $3->at(0));
       }
       else
       {
         $$ = drv.solver()->make_term(po, *$3);
       }
    }
    else if (apply_term = drv.lookup_symbol($2))
    {
      // UF
      smt::TermVec vec({apply_term});
      vec.insert(vec.end(), $3->begin(), $3->end());
      $$ = drv.solver()->make_term(smt::Apply, vec);
    }
    else if (apply_term = drv.lookup_selector($2))
    {
      // Datatype Selector
      smt::TermVec vec({apply_term});
      vec.insert(vec.end(), $3->begin(), $3->end());
      $$ = drv.solver()->make_term(smt::Apply_Selector, vec);
    }
    else if (apply_term = drv.lookup_constructor($2))
    {
      // Datatype Constructor
      smt::TermVec vec({apply_term});
      vec.insert(vec.end(), $3->begin(), $3->end());
      $$ = drv.solver()->make_term(smt::Apply_Constructor, vec);
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
    for (const auto attr : $4) {
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
      if (!sym && (sym = drv.lookup_constructor($1)))
      {
        // apply the constructor (even though there's no arguments, still need to apply)
        sym = drv.solver()->make_term(smt::Apply_Constructor, sym);
      }

      if (!sym)
      {
        // Note: using @1 will force locations to be enabled
        smtlib::parser::error(@1, std::string("Unrecognized symbol: ") + $1);
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

sort_dec:
   LP SYMBOL NAT RP
   {
     $$ = std::pair<std::string, std::size_t>($2, std::stoi($3));
   }
;

sort_decs:
   sort_dec
   {
     // not expecting large vectors
     // don't worry about copies (i.e., don't need to make it a pointer)
     std::vector<std::pair<std::string, std::size_t>> vec({$1});
     $$ = vec;
   }
   | sort_decs sort_dec
   {
     $1.push_back($2);
     $$ = $1;
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


indexed_op:
   indprefix SYMBOL NAT RP
   {
     smt::PrimOp po = drv.lookup_primop($2);
     if (po == smt::NUM_OPS_AND_NULL)
     {
       smtlib::parser::error(@2, "Unexpected symbol in indexed operator: " + $2);
     }
     $$ = {smt::Op(po, std::stoi($3)), nullptr};
   }
   | indprefix SYMBOL NAT NAT RP
   {
     smt::PrimOp po = drv.lookup_primop($2);
     if (po == smt::NUM_OPS_AND_NULL)
     {
       smtlib::parser::error(@2, "Unexpected symbol in indexed operator: " + $2);
     }
     $$ = {smt::Op(po, std::stoi($3), std::stoi($4)), nullptr};
   }
   | indprefix SYMBOL SYMBOL RP
   {
     $$ = drv.lookup_apply_op_term($2, $3);
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

datatypesym:
   SYMBOL
   {
      smt::SmtSolver & solver = drv.solver();
      smt::DatatypeDecl dtspec = solver->make_datatype_decl($1);
      smt::Sort dtfwdref = solver->make_datatype_sort_forward_ref(dtspec);
      drv.define_sort($1, dtfwdref);
      assert(dtspec);
      $$ = {dtspec, dtfwdref};
   }
;

datatypesorts:
   LP sort_decs RP
   {
      std::vector<std::pair<smt::DatatypeDecl, smt::Sort>> vec;
      smt::SmtSolver & solver = drv.solver();
      for (auto sd : $2)
      {
        std::string sortname = sd.first;
        if (sd.second > 0)
        {
          // TODO handle parametric datatypes
          smtlib::parser::error(@1,
                    "Parametric datatypes not yet supported in smt-switch");
          YYERROR;
        }
        smt::DatatypeDecl dtspec = solver->make_datatype_decl(sortname);
        smt::Sort dtfwdref = solver->make_datatype_sort_forward_ref(dtspec);
        drv.define_sort(sortname, dtfwdref);
        assert(dtspec); assert(dtfwdref);
        vec.push_back({dtspec, dtfwdref});
      }
      $$ = vec;
   }
;

datatypedecs:
  LP cons_list RP
  {
    std::vector<smt::ConstructorDecVec> vec({$2});
    $$ = vec;
  }
  | datatypedecs LP cons_list RP
  {
    $1.push_back($3);
    $$ = $1;
  }
;

cons_list:
   LP SYMBOL sel_list RP
   {
     // not expecing large vectors
     // don't worry about copies (i.e., don't need a pointer)
     smt::ConstructorDecVec vec({{$2, $3}});
     $$ = vec;
   }
   | cons_list LP SYMBOL sel_list RP
   {
     $1.push_back({$3, $4});
     $$ = $1;
   }
;

sel_list:
   %empty
   {
     // not expecing large vectors
     // don't worry about copies (i.e., don't need a pointer)
     smt::SelectorDecVec vec;
     $$ = vec;
   }
   | sel_list LP SYMBOL sort RP
   {
     $1.push_back({$3, $4});
     $$ = $1;
   }
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
     $$ = {$1, ""};
   }
   | KEYWORD s_expr
   {
     $$ = {$1, $2};
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

void smtlib::parser::error (const location_type& l, const std::string& m)
{
  cerr << l << ": " << m << endl;
}
