# Developer Information

## Style Decisions

* Formatting with `git-clang-format`
* Class names are capitalized
* Kind enums are all capitalized
* Operator enums use smt-lib names, but with the first letter (and letters after an underscore if it exists) capitalized
  * Exception: "bv" is always capitalized to "BV"
* Functions/methods are lower-cased with underscores
* Interface matches smt-lib closely

## Design Decisions

* Everything is a pointer
  * There are `using` statements which give convenient names so things may not *look* like pointers, but they are all shared_ptr to abstract base classes
  * In the solver implementations, the abstract class pointers are statically casted to the correct type. In particular, this means that mixing terms from different solvers will result in undefined behavior
* Modern C++
  * This library attempts to make use of modern C++ design paradigms whenever possible. In particular, we use C++17 for the support of constexpr arrays, and variants. 
  * The philosophy here is that it is better to rely on the new standard than adopt another dependency such as `boost`
* The abstract classes provide a common interface, but they were designed to give each solver as much flexibility as possible

There are three abstract classes:
* `AbsSmtSolver`
* `AbsSort`
* `AbsTerm`

Each one has a `using` declaration which provides a convenient name for a `shared_ptr` to the abstract class, e.g. `using Solver=std::shared_ptr<AbsSolver>`.


An `Op` is a simple struct that holds a `PrimOp` and up to two integer indices. The constructor for a single `PrimOp` is marked `explicit` so that there is no ambiguity in overloaded functions that take a `PrimOp` or an `Op`. Note: this could have workded by only taking an `Op`, but that would require constructing (either implicitly or explicitly) an `Op` object even if we just want to apply a `PrimOp`.

## Utils

There is an implementation of assertions and logging commands using `constexpr` functions in `include/utils.h`, these should be the only assertions/logging functions used throughout the codebase.


# Implementing New Solvers
As a general principle, smt-switch is meant to be as lightweight as possible. In other words, it should query the underlying solver for information (e.g. the sort of a term) whenever possible. To implement a new solver, look at the abstract classes in:
* `include/sort.h`
* `include/term.h`
* `include/solver.h`

You will need to implement a solver-specific version of each of those classes. To be able to build terms, you should map each operator in `include/ops.h`. Note that some methods have default implementations in `*.cpp` files under the `src` directory. These default implementations can be replaced with solver-specific implementations for performance improvements. For example, `substitute` takes a map and a term and performs sub-term substitution. This has a default implementation but is overriden in the `boolector` implementation to rely on `boolector's` underlying substitution map infrastructure.

All your solver header and source files should be put in `<solver name>/include` and `<solver name>/src`, respectively.

Finally, you would make a `create` method which can instantiate a pointer to your new solver. For example, see `include/cvc4_factory.h`.
