#pragma once

#include <string>

#include "smtlibparser.h"

#define YY_DECL yy::parser::symbol_type yylex(SmtLibDriver & drv)
YY_DELC;

class SmtLibDriver
{
 public:
  SmtLibDriver();

  int parse(const std::string & f);
  // The name of the file being parsed.
  std::string file;

  void scan_begin();
  void scan_end();

  yy::location location;
}
