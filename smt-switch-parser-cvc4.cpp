#include <iostream>

#include "smt-switch/cvc4_factory.h"
#include "smtlib_reader.h"

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
  SmtLibReader drv(solver);
  if (drv.parse (argv[1]))
  {
    std::cout << "FAILED" << std::endl;
    res = 1;
  }
  return res;
}
