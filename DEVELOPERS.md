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

There are four abstract classes:
* `AbsSmtSolver`
* `AbsSort`
* `AbsFun`
* `AbsTerm`

Each one has a `using` declaration which provides a convenient name for a `shared_ptr` to the abstract class, e.g. `using Solver=std::shared_ptr<AbsSolver>`.


An `Op` is a simple struct that holds a `PrimOp` and up to two integer indices. The constructor for a single `PrimOp` is marked `explicit` so that there is no ambiguity in overloaded functions that take a `PrimOp` or an `Op`. Note: this could have workded by only taking an `Op`, but that would require constructing (either implicitly or explicitly) an `Op` object even if we just want to apply a `PrimOp`.

## Utils

There is an implementation of assertions and logging commands using `constexpr` functions in `include/utils.h`, these should be the only assertions/logging functions used throughout the codebase.


# Boolector Notes

Boolector does not expose the children of a node, nor the operation that was used to obtain a node. Thus, in this implementation for Boolector, we track those things at the generic API level. Furthermore,  Boolector queries nodes for type information (e.g. width of a bit-vector) rather than sorts. Thus, we also have a heavier-weight implementation of the sort class for Boolector that maintains the sort parameters.

Other solver implementations might not track these parameters directly, but instead query the underlying solver. It's possible that querying the solver each time may actually be slower, but that will take some benchmarking to evaluate. Notice that if we are performing unrolling for bounded model checking, we will need to traverse the formula each time and rebuild the nodes. Traversing the formula requires looking up the children and the operation. If we query the solver for these each time, it requires re-wrapping those objects in the generic API's data structures each time. This might be slower than just keeping a pointer to the operation and the children in the generic API's term object.
