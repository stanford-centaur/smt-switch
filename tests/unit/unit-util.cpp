#include "utils.h"

int main()
{
  Log<0>("message!");
  Log<1>("no message!");
#ifdef _DEBUG
  Assert(true);
#else
  // should compile to nothing
  Assert(false);
#endif
  return 0;
}
