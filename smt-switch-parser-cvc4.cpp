#include <iostream>
#include "smtlib_driver.h"
#include "smt-switch/cvc4_factory.h"

using namespace smt;

int main (int argc, char *argv[])
{
  if (argc != 2)
  {
    std::cout << "usage: " << argv[0] << " <smt-lib2 file>" << std::endl;
    return 1;
  }
  int res = 0;
  SmtSolver solver = CVC4SolverFactory::create(false);
  SmtLibDriver drv(solver);
  if (drv.parse (argv[1]))
  {
    std::cout << "FAILED" << std::endl;
    res = 1;
  }
  return res;
}
