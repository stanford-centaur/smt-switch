# generic-smt-api
A generic C++ API for SMT solving. It provides abstract classes which can be implemented by different SMT solvers.

# Architecture Overview

There are four abstract classes:
* `AbsSmtSolver`
* `AbsSort`
* `AbsFun`
* `AbsTerm`

Each of them has a `using` statement that names a smart pointer of that type, e.g. `using Term = shared_ptr<AbsTerm>;`. They all use `shared_ptr`s except `SmtSolver` which is a `unique_ptr` to an `AbsSmtSolver`. The key thing to remember when using this library is that all solver-specific objects are pointers to the abstract base class. `SmtSolver`, `Sort`, `Fun`, and `Term` are all smart pointers. Note: there are many convenience functions which operate on these pointers, so they may not *look* like pointers. Additionally, the library also includes `using` statements for commonly used data structures, for example, `TermVec` is a vector of shared pointers to `AbsTerm`s.

The function names are based on SMT-LIB. The general rule is that functions/methods in this library can be obtained syntactically from SMT-LIB commands by replacing dashes with underscores. There are a few exceptions, for example `assert` is `assert_formula` in this library to avoid clashing with the `assert` macro. Operator names are also based on SMT-LIB operators, and can be obtained syntactically from an SMT-LIB operator by capitalizing the first letter and any letter after an underscore. The only exception is `bv` which is always capitalized to `BV` and does not count towards the capitalization of the first letter. Some examples include:

* `And`
* `BVAnd`
* `Zero_Extend`
* `BVAshr`

Please see the `tests` directory for some example usage.
