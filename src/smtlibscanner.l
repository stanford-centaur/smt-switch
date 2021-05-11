%{
/*********************                                                        */
/*! \file smtlibscanner.[l/cpp]
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Flex file and auto-generated scanner.
**
**
**/
#include <iostream>
#include "stdio.h"
#include "smtlib_reader.h"
#include "smtlibparser.h"
using namespace std;
%}

%option noyywrap nounput noinput batch
/* can uncomment next line to give debug output during lexing */
/* %option debug */

bvarithop bv(neg|add|sub|mul)
bvbwop bv(not|and|or|xor|nand|nor|xnor|comp)
bvusop bv[us](div|rem|lt|le|ge|gt)
bvshop bv(shl|ashr|lshr)
bvmanipop (concat|extract|zero_extend|sign_extend|repeat|rotate_left|rotate_right)

symbol [a-zA-Z~!@\$%\^&\*+=<>\.\?/_-]+[a-zA-Z0-9~!@\$%\^&\*+=<>\.\?/_-]*

%%

[ \t\r]+              ;
\n+                   ;

\;.*                  ;/* skip comment */

\(                    { return yy::parser::make_LP(); }
\)                    { return yy::parser::make_RP(); }
_                     { return yy::parser::make_US(); }

set-logic             { return yy::parser::make_SETLOGIC(); }
set-option            { return yy::parser::make_SETOPT(); }
set-info              { return yy::parser::make_SETINFO(); }
declare-const         { return yy::parser::make_DECLARECONST(); }
declare-fun           { return yy::parser::make_DECLAREFUN(); }
define-fun            { return yy::parser::make_DEFINEFUN(); }
define-sort           { return yy::parser::make_DEFINESORT(); }
assert                { return yy::parser::make_ASSERT(); }
check-sat             { return yy::parser::make_CHECKSAT(); }
check-sat-assuming    { return yy::parser::make_CHECKSATASSUMING(); }
push                  { return yy::parser::make_PUSH(); }
pop                   { return yy::parser::make_POP(); }
exit                  { return yy::parser::make_EXIT(); }
get-value[ \t\r]*\(   { return yy::parser::make_GETVALUELP(); }
get-unsat-assumptions { return yy::parser::make_GETUNSATASSUMP(); }
echo                  { return yy::parser::make_ECHO(); }

\"(\\.|[^\"\\])*\"    { char * noquotes = yytext;
                        noquotes++;
                        noquotes[strlen(noquotes)-1] = 0;
                        return yy::parser::make_QUOTESTRING(noquotes);
                      }

[0-9]+                { return yy::parser::make_NAT(yytext); }
[0-9]+\.[0-9]+        { return yy::parser::make_FLOAT(yytext); }
#b[01]+               { yytext=yytext+2; return yy::parser::make_BITSTR(yytext); }
#x[0-9a-fA-F]+        { yytext=yytext+2; return yy::parser::make_HEXSTR(yytext); }
bv[0-9]+              { yytext=yytext+2; return yy::parser::make_BVDEC(yytext); }
as[ \t\r\n]+const     { return yy::parser::make_ASCONST(); }
let                   { return yy::parser::make_LET(); }

\:[a-zA-Z0-9_-]+      { return yy::parser::make_KEYWORD(++yytext); }

Bool                  { return yy::parser::make_BOOL(); }
Int                   { return yy::parser::make_INT(); }
Real                  { return yy::parser::make_REAL(); }
BitVec                { return yy::parser::make_BITVEC(); }
Array                 { return yy::parser::make_ARRAY(); }

(and|or|xor|not)      { return yy::parser::make_PRIMOP(yytext); }
(=>)                  { return yy::parser::make_PRIMOP(yytext); }
(=|distinct)          { return yy::parser::make_PRIMOP(yytext); }
ite                   { return yy::parser::make_PRIMOP(yytext); }
[+*/-]                { return yy::parser::make_PRIMOP(yytext); }
(<|>)(=?)             { return yy::parser::make_PRIMOP(yytext); }
{bvarithop}           { return yy::parser::make_PRIMOP(yytext); }
{bvbwop}              { return yy::parser::make_PRIMOP(yytext); }
{bvusop}              { return yy::parser::make_PRIMOP(yytext); }
bvsmod                { return yy::parser::make_PRIMOP(yytext); }
{bvshop}              { return yy::parser::make_PRIMOP(yytext); }
{bvmanipop}           { return yy::parser::make_PRIMOP(yytext); }
(select|store)        { return yy::parser::make_PRIMOP(yytext); }
(forall|exists)       { return yy::parser::make_QUANTIFIER(yytext); }

\|([^|\\])*\|         {
                        // get rid of pipe quotes
                        yytext++;
                        yytext[strlen(yytext)-1] = '\0';
                        return yy::parser::make_SYMBOL(yytext);
                      }
{symbol}              { return yy::parser::make_SYMBOL(yytext); }

.                     { throw SmtException(std::string("Parser ERROR on: ") + yytext); }
<<EOF>>               { return yy::parser::make_YYEOF (); }
%%

void smt::SmtLibReader::scan_begin ()
{
  // commented from calc++ example -- could consider adding for debug support
  /* yy_flex_debug = trace_scanning; */
  if (file.empty () || file == "-")
    yyin = stdin;
  else if (!(yyin = fopen (file.c_str (), "r")))
  {
    std::cerr << "cannot open " << file << ": " << strerror (errno) << '\n';
    exit (EXIT_FAILURE);
  }
}

void smt::SmtLibReader::scan_end ()
{
  fclose (yyin);
}
