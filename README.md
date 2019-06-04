# generic-smt-api
A generic C++ API for SMT solving. It provides abstract classes which can be implemented by different SMT solvers.

# Architecture Overview

This implementation is currently a header-only library. There are four abstract classes:
* `AbsSmtSolver`
* `AbsSort`
* `AbsFunc`
* `AbsTerm`

Each of them has a `using` statement that names a `shared_ptr` of that type, e.g. `using SmtSolver = shared_ptr<AbsSmtSolver>;`. The key thing to remember when using this library is that everything is a pointer (with the exception of an `Op` which is just a struct). There are many convenience functions which operator on shared pointers to these abstract classes, so they may not *look* like pointer. Additionally, there are `using` statements for commonly used data structures, for example, `TermVec` is a vector of shared pointers to `AbsTerm`s.

Please see the `tests` directory for some example usage.
