#include <iostream>
#include "smtlib_driver.h"
#include "smt-switch/cvc4_factory.h"

using namespace smt;

int main (int argc, char *argv[])
{
  int res = 0;
  SmtSolver solver = CVC4SolverFactory::create(false);
  SmtLibDriver drv(solver);
  for (int i = 1; i < argc; ++i)
    if (!drv.parse (argv[i]))
    {
      std::cout << "Finished parsing" << std::endl;
    }
    else
    {
      std::cout << "FAILED" << std::endl;
      res = 1;
    }
  return res;
}
