#include "test-utils.h"

using namespace std;
using namespace smt;

namespace smt_tests {

UnorderedTermSet get_free_symbols(Term & t)
{
  UnorderedTermSet free_symbols;
  TermVec to_visit({ t });
  UnorderedTermSet visited;

  Term n;
  while (to_visit.size())
  {
    n = to_visit.back();
    to_visit.pop_back();

    if (visited.find(n) == visited.end())
    {
      visited.insert(n);
      for (auto nn : n)
      {
        to_visit.push_back(nn);
      }

      if (n->is_symbolic_const())
      {
        free_symbols.insert(n);
      }
    }
  }

  return free_symbols;
}

}  // namespace smt_tests
