/*!
 * \file smtlib_scanner.l
 * \brief The SMT-LIB tokens, from which flex generates the scanner
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
%option batch
%option c++
%option noinput
%option nounistd
%option nounput
%option noyywrap
%option prefix="smtlib"

/* Emitted at the start of smtlib_scanner.cpp, before flex's code */
%top{
// The scanner defines macros that use this class before it is declared.
class smtlibFlexLexer;

// This and the end_keep below suppress IWYU removals for the generated code.
// IWYU pragma: begin_keep
}

%{
// IWYU pragma: end_keep

#include <memory>
#include <string>

#include "smt-switch/exceptions.h"
#include "smt-switch/text_utils.h"
#include "smtlib_parser.h"

// The generated scanner code uses the C spelling.
// IWYU pragma: no_include <cerrno>

// Bug in IWYU (this forward declaration is not valid C++)
// IWYU pragma: no_forward_declare smt::SmtLibScanner::Lexer

namespace smt {

/** The scanner flex generates, which moves the location along as it reads */
class SmtLibScanner::Lexer : public smtlibFlexLexer
{
 public:
  Lexer(std::istream & input, SmtLibParser::location_type & location);

  /** Reads the next token of the input */
  SmtLibParser::symbol_type next_token();

 private:
  /** Throws the errors flex cannot recover from, such as a failed read or
   *  allocation, which it would otherwise print before exiting
   */
  void LexerError(const char * msg) override;

  SmtLibParser::location_type & loc;
};

}  // namespace smt

// The scanner's yylex, renamed and returning the parser's symbols. flex
// defines yyFlexLexer::yylex unless this is defined first.
#define YY_DECL \
  smt::SmtLibParser::symbol_type smt::SmtLibScanner::Lexer::next_token()

// The length of the token, as the location counts it. Some flex versions
// declare yyleng as an int and others as a size_t. A token too long for
// the count would only misplace the columns of a later error.
#define TOKEN_LENGTH \
  static_cast<smt::SmtLibParser::location_type::counter_type>(yyleng)

#define YY_USER_ACTION loc.step(); loc.columns(TOKEN_LENGTH);
%}

simplesymbol [a-zA-Z~!@\$%\^&\*+=<>\.\?/_-][a-zA-Z0-9~!@\$%\^&\*+=<>\.\?/_-]*

%%

[ \t\r]+              { /* skip whitespace */ }
\n+                   { loc.lines(TOKEN_LENGTH); }

;.*                   { /* skip comment */ }

\(                    { return SmtLibParser::make_LP(loc); }
\)                    { return SmtLibParser::make_RP(loc); }
_                     { return SmtLibParser::make_US(yytext, loc); }
!                     { return SmtLibParser::make_EP(yytext, loc); }

set-logic             { return SmtLibParser::make_SETLOGIC(yytext, loc); }
set-option            { return SmtLibParser::make_SETOPT(yytext, loc); }
set-info              { return SmtLibParser::make_SETINFO(yytext, loc); }
declare-const         { return SmtLibParser::make_DECLARECONST(yytext, loc); }
declare-fun           { return SmtLibParser::make_DECLAREFUN(yytext, loc); }
declare-sort          { return SmtLibParser::make_DECLARESORT(yytext, loc); }
define-fun            { return SmtLibParser::make_DEFINEFUN(yytext, loc); }
define-sort           { return SmtLibParser::make_DEFINESORT(yytext, loc); }
assert                { return SmtLibParser::make_ASSERT(yytext, loc); }
check-sat             { return SmtLibParser::make_CHECKSAT(yytext, loc); }
check-sat-assuming    { return SmtLibParser::make_CHECKSATASSUMING(yytext, loc); }
push                  { return SmtLibParser::make_PUSH(yytext, loc); }
pop                   { return SmtLibParser::make_POP(yytext, loc); }
exit                  { return SmtLibParser::make_EXIT(yytext, loc); }
get-value             { return SmtLibParser::make_GETVALUE(yytext, loc); }
get-unsat-assumptions { return SmtLibParser::make_GETUNSATASSUMP(yytext, loc); }
echo                  { return SmtLibParser::make_ECHO(yytext, loc); }

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
as[ \t\r\n]+const     { return SmtLibParser::make_ASCONST("as const", loc); }
let                   { return SmtLibParser::make_LET(yytext, loc); }

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
                        return SmtLibParser::make_SYMBOL(
                            smtlib::unquote_symbol(yytext), loc);
                      }
{simplesymbol}        { return SmtLibParser::make_SYMBOL(yytext, loc); }

.                     { return SmtLibParser::make_SMTLIBUNDEF(loc); }
<<EOF>>               { loc.step(); return SmtLibParser::make_SMTLIBEOF(loc); }
%%

// flex's own yylex, which the vtable needs although YY_DECL replaces it
int smtlibFlexLexer::yylex()
{
  throw smt::InternalException("The SMT-LIB scanner has no yylex");
}

namespace smt {

SmtLibScanner::Lexer::Lexer(std::istream & input,
                            SmtLibParser::location_type & location)
    : smtlibFlexLexer(&input), loc(location)
{
}

void SmtLibScanner::Lexer::LexerError(const char * msg)
{
  throw SystemException(msg);
}

SmtLibScanner::SmtLibScanner(std::istream & input,
                             SmtLibParser::location_type & location)
    : lexer(std::make_unique<Lexer>(input, location))
{
}

SmtLibScanner::~SmtLibScanner() = default;

SmtLibParser::symbol_type SmtLibScanner::next_token()
{
  return lexer->next_token();
}

}  // namespace smt
