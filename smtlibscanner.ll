%{
#include <iostream>
#include "stdio.h"
#include "smtlib_driver.h"
#include "smtlibparser.h"
using namespace std;
%}

%option noyywrap nounput noinput batch debug

%{
  // Code run each time a pattern is matched.
# define YY_USER_ACTION  loc.columns (yyleng);
%}

%%

%{
  // A handy shortcut to the location held by the driver.
  yy::location& loc = drv.location;
  // Code run each time yylex is called.
  loc.step ();
%}

[(]               { return yy::parser::make_LP(loc); }
[)]               { return yy::parser::make_RP(loc); }
[a-zA-Z0-9_-]+    { return yy::parser::make_SYMBOL(loc); }
[ \t]             ; //ignore all whitespace
.                 { cout << "ERROR: no match for " << yytext << endl; }

%%

void SmtLibDriver::scan_begin ()
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

void
SmtLibDriver::scan_end ()
{
  fclose (yyin);
}
