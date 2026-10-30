/*!
 * \file smtlibscanner.l
 * \brief The SMT-LIB tokens, from which flex generates the scanner.
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
%option batch
%option extra-type="smtlib::location *"
%option noinput
%option nounput
%option noyywrap
%option prefix="smtlib"
%option reentrant

%{
#include <cstring>
#include <stdexcept>

#include "smtlibparser.h"

#define YY_USER_ACTION loc.step(); loc.columns(yyleng);

// Errors flex cannot recover from, such as a failed read or allocation,
// which it would otherwise print before exiting.
#define YY_FATAL_ERROR(msg) throw std::runtime_error(msg)
%}

simplesymbol [a-zA-Z~!@\$%\^&\*+=<>\.\?/_-][a-zA-Z0-9~!@\$%\^&\*+=<>\.\?/_-]*

%%

%{
  smtlib::location & loc = *yyextra;
%}
[ \t\r]+              { /* skip whitespace */ }
\n+                   { loc.lines(yyleng); }

;.*                   { /* skip comment */ }

\(                    { return smtlib::parser::make_LP(loc); }
\)                    { return smtlib::parser::make_RP(loc); }
_                     { return smtlib::parser::make_US(loc); }
!                     { return smtlib::parser::make_EP(loc); }

set-logic             { return smtlib::parser::make_SETLOGIC(loc); }
set-option            { return smtlib::parser::make_SETOPT(loc); }
set-info              { return smtlib::parser::make_SETINFO(loc); }
declare-const         { return smtlib::parser::make_DECLARECONST(loc); }
declare-fun           { return smtlib::parser::make_DECLAREFUN(loc); }
declare-sort          { return smtlib::parser::make_DECLARESORT(loc); }
define-fun            { return smtlib::parser::make_DEFINEFUN(loc); }
define-sort           { return smtlib::parser::make_DEFINESORT(loc); }
assert                { return smtlib::parser::make_ASSERT(loc); }
check-sat             { return smtlib::parser::make_CHECKSAT(loc); }
check-sat-assuming    { return smtlib::parser::make_CHECKSATASSUMING(loc); }
push                  { return smtlib::parser::make_PUSH(loc); }
pop                   { return smtlib::parser::make_POP(loc); }
exit                  { return smtlib::parser::make_EXIT(loc); }
get-value[ \t\r]*     { return smtlib::parser::make_GETVALUE(loc); }
get-unsat-assumptions { return smtlib::parser::make_GETUNSATASSUMP(loc); }
echo                  { return smtlib::parser::make_ECHO(loc); }

\"(\\.|[^\"\\])*\"    {
                        char * noquotes = yytext;
                        noquotes++;
                        noquotes[std::strlen(noquotes) - 1] = 0;
                        // increment location for each line
                        for (const char * c = noquotes; *c; ++c)
                        {
                          if (*c == '\n')
                          {
                            loc.lines(1);
                          }
                        }
                        loc.step();
                        return smtlib::parser::make_QUOTESTRING(noquotes, loc);
                      }

[0-9]+                { return smtlib::parser::make_NAT(yytext, loc); }
[0-9]+\.[0-9]+        { return smtlib::parser::make_FLOAT(yytext, loc); }
#b[01]+               { yytext = yytext + 2; return smtlib::parser::make_BITSTR(yytext, loc); }
#x[0-9a-fA-F]+        { yytext = yytext + 2; return smtlib::parser::make_HEXSTR(yytext, loc); }
as[ \t\r\n]+const     { return smtlib::parser::make_ASCONST(loc); }
let                   { return smtlib::parser::make_LET(loc); }

\:{simplesymbol}      { return smtlib::parser::make_KEYWORD(++yytext, loc); }

(forall|exists)       { return smtlib::parser::make_QUANTIFIER(yytext, loc); }

\|([^|\\])*\|         {
                        // increment location for each line
                        for (const char * c = yytext; *c; ++c)
                        {
                          if (*c == '\n')
                          {
                            loc.lines(1);
                          }
                        }
                        loc.step();
                        // get rid of pipe quotes
                        yytext++;
                        yytext[std::strlen(yytext) - 1] = '\0';
                        return smtlib::parser::make_SYMBOL(yytext, loc);
                      }
{simplesymbol}        { return smtlib::parser::make_SYMBOL(yytext, loc); }

.                     { return smtlib::parser::make_SMTLIBUNDEF(loc); }
<<EOF>>               { loc.step(); return smtlib::parser::make_SMTLIBEOF(loc); }
%%
