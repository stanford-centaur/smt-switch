#pragma once
#include <string>

#ifndef yyFlexLexerOnce
#include <FlexLexer.h>
#endif

#include "smtlib.h"

// TODO add a namespace
namespace smt
{

class SmtLibLexer : public yyFlexLexer
{
 public:
  // might need to pass a parser
  SmtLibLexer() {}

  virtual smt::smtlib::symbol_type smtliblex();
};

}
