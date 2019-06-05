# generic-smt-api
A generic C++ API for SMT solving. It provides abstract classes which can be implemented by different SMT solvers.

# Architecture Overview

This implementation is currently a header-only library. There are four abstract classes:
* `AbsSmtSolver`
* `AbsSort`
* `AbsFunc`
* `AbsTerm`

Each of them has a `using` statement that names a `shared_ptr` of that type, e.g. `using SmtSolver = shared_ptr<AbsSmtSolver>;`. The key thing to remember when using this library is that all solver-specific objects are pointers to the abstract base class. E.g. `SmtSolver`, `Sort`, `Func`, and `Term` are all shared pointers. Note: there are many convenience functions which operate on these shared pointers, so they may not *look* like pointers. Additionally, the library also includes `using` statements for commonly used data structures, for example, `TermVec` is a vector of shared pointers to `AbsTerm`s.

Please see the `tests` directory for some example usage.
