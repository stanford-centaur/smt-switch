#include "smtlib_driver.h"
#include "smtlibparser.h"

SmtLibDriver::SmtLibDriver()
{}

int SmtLibDriver::parse(const std::string & f)
{
  file = f;
  location_.initialize(&file);
  scan_begin();
  yy::parser parse(*this);
  // commented from calc++ example
  //parse.set_debug_level (trace_parsing);
  int res = parse();
  scan_end();
  return res;
}
