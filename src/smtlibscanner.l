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

symbol [a-zA-Z~!@\$%\^&\*+=<>\.\?/_-][a-zA-Z0-9~!@\$%\^&\*+=<>\.\?/_-]*

%{
  // Code run each time a pattern is matched.
# define YY_USER_ACTION  loc.columns (yyleng);
%}

%%

%{
  // A handy shortcut to the location held by the driver.
  yy::location& loc = drv.location();
  // Code run each time yylex is called.
  loc.step ();
%}
[ \t\r]+              loc.step ();
\n+                   loc.lines (yyleng); loc.step ();

\;.*                  ;/* skip comment */

\(                    { return yy::parser::make_LP(loc); }
\)                    { return yy::parser::make_RP(loc); }
_                     { return yy::parser::make_US(loc); }

set-logic             { return yy::parser::make_SETLOGIC(loc); }
set-option            { return yy::parser::make_SETOPT(loc); }
set-info              { return yy::parser::make_SETINFO(loc); }
declare-const         { return yy::parser::make_DECLARECONST(loc); }
declare-fun           { return yy::parser::make_DECLAREFUN(loc); }
define-fun            { return yy::parser::make_DEFINEFUN(loc); }
define-sort           { return yy::parser::make_DEFINESORT(loc); }
assert                { return yy::parser::make_ASSERT(loc); }
check-sat             { return yy::parser::make_CHECKSAT(loc); }
check-sat-assuming    { return yy::parser::make_CHECKSATASSUMING(loc); }
push                  { return yy::parser::make_PUSH(loc); }
pop                   { return yy::parser::make_POP(loc); }
exit                  { return yy::parser::make_EXIT(loc); }
get-value[ \t\r]*     { return yy::parser::make_GETVALUE(loc); }
get-unsat-assumptions { return yy::parser::make_GETUNSATASSUMP(loc); }
echo                  { return yy::parser::make_ECHO(loc); }

\"(\\.|[^\"\\])*\"    { char * noquotes = yytext;
                        noquotes++;
                        noquotes[strlen(noquotes)-1] = 0;
                        // increment location for each line
                        for (const char * c=noquotes; *c; ++c)
                        {
                          if(*c == '\n')
                          {
                            loc.lines(1);
                          }
                        }
                        loc.step();
                        return yy::parser::make_QUOTESTRING(noquotes, loc);
                      }

[0-9]+                { return yy::parser::make_NAT(yytext, loc); }
[0-9]+\.[0-9]+        { return yy::parser::make_FLOAT(yytext, loc); }
#b[01]+               { yytext=yytext+2; return yy::parser::make_BITSTR(yytext, loc); }
#x[0-9a-fA-F]+        { yytext=yytext+2; return yy::parser::make_HEXSTR(yytext, loc); }
bv[0-9]+              { yytext=yytext+2; return yy::parser::make_BVDEC(yytext, loc); }
as[ \t\r\n]+const     { return yy::parser::make_ASCONST(loc); }
let                   { return yy::parser::make_LET(loc); }

\:[a-zA-Z0-9_-]+      { return yy::parser::make_KEYWORD(++yytext, loc); }

(forall|exists)       { return yy::parser::make_QUANTIFIER(yytext, loc); }

\|([^|\\])*\|         {
                        // increment location for each line
                        for (const char * c=yytext; *c; ++c)
                        {
                          if(*c == '\n')
                          {
                            loc.lines(1);
                          }
                        }
                        loc.step();
                        // get rid of pipe quotes
                        yytext++;
                        yytext[strlen(yytext)-1] = '\0';
                        return yy::parser::make_SYMBOL(yytext, loc);
                      }
{symbol}              { return yy::parser::make_SYMBOL(yytext, loc); }

.                     { throw SmtException(std::string("Parser ERROR on: ") + yytext); }
<<EOF>>               { return yy::parser::make_YYEOF (loc); }
%%

void smt::SmtLibReader::scan_begin ()
{
  // flush the buffer to make sure scanner state is fresh
  YY_FLUSH_BUFFER;
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
