/*!
 * \file smtlib_scanner.l
 * \brief The SMT-LIB tokens, from which flex generates the scanner.
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
%option batch
%option extra-type="smt::SmtLibParser::location_type *"
%option noinput
%option nounput
%option noyywrap
%option prefix="smtlib"
%option reentrant

/* Emitted into smtlib_scanner.h and smtlib_scanner.cpp, before flex's code. */
%top{
#include <cstdio>

#include "smtlib_parser.h"

// The scanner's state, as flex defines it further down, too late for the
// declarations below.
#ifndef YY_TYPEDEF_YY_SCANNER_T
#define YY_TYPEDEF_YY_SCANNER_T
typedef void * yyscan_t;
#endif

// The scanner's yylex, renamed by the prefix and put in smt, so that the
// rules below use the names in smt. flex declares an int yylex unless this
// is defined first.
#define YY_DECL \
  smt::SmtLibParser::symbol_type smt::smtliblex(yyscan_t yyscanner)

namespace smt {

/** The scanner's yylex, as YY_DECL defines it */
SmtLibParser::symbol_type smtliblex(yyscan_t yyscanner);

/** The scanner of one input, which owns flex's state for it */
class SmtLibScanner
{
 public:
  /** @param input the input to read
   *  @param loc where the scanner is in the input, which it moves along
   *  @throws std::bad_alloc if flex cannot allocate its state
   */
  SmtLibScanner(std::FILE * input, SmtLibParser::location_type & loc);
  SmtLibScanner(const SmtLibScanner &) = delete;
  SmtLibScanner & operator=(const SmtLibScanner &) = delete;
  ~SmtLibScanner();

  /** Reads the next token of the input */
  SmtLibParser::symbol_type next_token();

 private:
  yyscan_t state_;
};

/** The parser's yylex, renamed by the prefix */
inline SmtLibParser::symbol_type smtliblex(SmtLibScanner & scanner)
{
  return scanner.next_token();
}

}  // namespace smt
}

%{
#include <cstring>
#include <new>
#include <stdexcept>

#define YY_USER_ACTION loc.step(); loc.columns(yyleng);

// Errors flex cannot recover from, such as a failed read or allocation,
// which it would otherwise print before exiting.
#define YY_FATAL_ERROR(msg) throw std::runtime_error(msg)
%}

simplesymbol [a-zA-Z~!@\$%\^&\*+=<>\.\?/_-][a-zA-Z0-9~!@\$%\^&\*+=<>\.\?/_-]*

%%

%{
  SmtLibParser::location_type & loc = *yyextra;
%}
[ \t\r]+              { /* skip whitespace */ }
\n+                   { loc.lines(yyleng); }

;.*                   { /* skip comment */ }

\(                    { return SmtLibParser::make_LP(loc); }
\)                    { return SmtLibParser::make_RP(loc); }
_                     { return SmtLibParser::make_US(loc); }
!                     { return SmtLibParser::make_EP(loc); }

set-logic             { return SmtLibParser::make_SETLOGIC(loc); }
set-option            { return SmtLibParser::make_SETOPT(loc); }
set-info              { return SmtLibParser::make_SETINFO(loc); }
declare-const         { return SmtLibParser::make_DECLARECONST(loc); }
declare-fun           { return SmtLibParser::make_DECLAREFUN(loc); }
declare-sort          { return SmtLibParser::make_DECLARESORT(loc); }
define-fun            { return SmtLibParser::make_DEFINEFUN(loc); }
define-sort           { return SmtLibParser::make_DEFINESORT(loc); }
assert                { return SmtLibParser::make_ASSERT(loc); }
check-sat             { return SmtLibParser::make_CHECKSAT(loc); }
check-sat-assuming    { return SmtLibParser::make_CHECKSATASSUMING(loc); }
push                  { return SmtLibParser::make_PUSH(loc); }
pop                   { return SmtLibParser::make_POP(loc); }
exit                  { return SmtLibParser::make_EXIT(loc); }
get-value[ \t\r]*     { return SmtLibParser::make_GETVALUE(loc); }
get-unsat-assumptions { return SmtLibParser::make_GETUNSATASSUMP(loc); }
echo                  { return SmtLibParser::make_ECHO(loc); }

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
                        return SmtLibParser::make_QUOTESTRING(noquotes, loc);
                      }

[0-9]+                { return SmtLibParser::make_NAT(yytext, loc); }
[0-9]+\.[0-9]+        { return SmtLibParser::make_FLOAT(yytext, loc); }
#b[01]+               { yytext = yytext + 2; return SmtLibParser::make_BITSTR(yytext, loc); }
#x[0-9a-fA-F]+        { yytext = yytext + 2; return SmtLibParser::make_HEXSTR(yytext, loc); }
as[ \t\r\n]+const     { return SmtLibParser::make_ASCONST(loc); }
let                   { return SmtLibParser::make_LET(loc); }

\:{simplesymbol}      { return SmtLibParser::make_KEYWORD(++yytext, loc); }

(forall|exists)       { return SmtLibParser::make_QUANTIFIER(yytext, loc); }

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
                        return SmtLibParser::make_SYMBOL(yytext, loc);
                      }
{simplesymbol}        { return SmtLibParser::make_SYMBOL(yytext, loc); }

.                     { return SmtLibParser::make_SMTLIBUNDEF(loc); }
<<EOF>>               { loc.step(); return SmtLibParser::make_SMTLIBEOF(loc); }
%%

namespace smt {

SmtLibScanner::SmtLibScanner(std::FILE * input,
                             SmtLibParser::location_type & loc)
{
  if (smtliblex_init_extra(&loc, &state_) != 0)
  {
    throw std::bad_alloc();
  }
  smtlibset_in(input, state_);
}

SmtLibScanner::~SmtLibScanner() { smtliblex_destroy(state_); }

SmtLibParser::symbol_type SmtLibScanner::next_token()
{
  return smtliblex(state_);
}

}  // namespace smt
