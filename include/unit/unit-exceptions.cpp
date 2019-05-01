#include "exceptions.h"

#include "assert.h"

int throw_exception() { throw SmtException("test"); }

bool catch_exception() {
  try {
    throw_exception();
    return false;
  } catch (SmtException &e) {
    return true;
  } catch (...) {
    return false;
  }
}

int main() { assert(catch_exception()); }
