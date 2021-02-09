%{
#include <iostream>
//#include "location.hh"
#include "smtlib_lexer.h"
#undef YY_DECL
#define YY_DECL smt::smtlib::symbol_type SmtLibLexer::smtliblex ()
YY_DECL
using namespace std;
%}
%option c++
%option noyywrap
%option yyclass="SmtLibLexer"
%option prefix="smtlib"
%%
[(]               { return parser::make_LP(); }
[)]               { return parser::make_RP(); }
[a-zA-Z0-9_-]+    { return parser::make_SYMBOL(); }
[ \t]             ; //ignore all whitespace
.                 { cout << "ERROR: no match for " << yytext << endl; }
%%
