#include <iostream>
#include "smtlib_driver.h"

int
main (int argc, char *argv[])
{
  int res = 0;
  SmtLibDriver drv;
  for (int i = 1; i < argc; ++i)
    if (!drv.parse (argv[i]))
      std::cout << drv.result << '\n';
    else
      res = 1;
  return res;
}
