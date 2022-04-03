# Smt-Switch
A generic C++ API for SMT solving. It provides abstract classes which can be implemented by different SMT solvers.

# Quick Start
```
$ git clone git@github.com:stanford-centaur/smt-switch.git
$ cd smt-switch 
$ ./contrib/setup-<solver>.sh
$ ./configure.sh --<solver>
$ cd build 
$ make 
$ make test
```
More details are in the Solvers section of this README. 

For an example of how to link and use `smt-switch`, please see the [examples directory](./examples).

# Architecture Overview

There are three abstract classes:
* `AbsSmtSolver`
* `AbsSort`
* `AbsTerm`

Each of them has a `using` statement that names a smart pointer of that type, e.g. `using Term = shared_ptr<AbsTerm>;`. The key thing to remember when using this library is that all solver-specific objects are pointers to the abstract base class. `SmtSolver`, `Sort`, and `Term` are all smart pointers. Note: there are many convenience functions which operate on these pointers, so they may not *look* like pointers. Additionally, the library also includes `using` statements for commonly used data structures, for example, `TermVec` is a vector of shared pointers to `AbsTerm`s.

The function names are based on SMT-LIB. The general rule is that functions/methods in this library can be obtained syntactically from SMT-LIB commands by replacing dashes with underscores. There are a few exceptions, for example `assert` is `assert_formula` in this library to avoid clashing with the `assert` macro. Operator names are also based on SMT-LIB operators, and can be obtained syntactically from an SMT-LIB operator by capitalizing the first letter and any letter after an underscore. The only exception is `bv` which is always capitalized to `BV` and does not count towards the capitalization of the first letter. Some examples include:

* `And`
* `BVAnd`
* `Zero_Extend`
* `BVAshr`

Please see this [extended abstract](https://arxiv.org/abs/2007.01374) for more documentation or the `tests` directory for some example usage.

# Creating a Smt-Switch Solver
To create a Smt-Switch solver through the API, first include the relevant factory header and then use the static `create` method. It takes a single boolean parameter which configures term logging. If passed `false`, the created `SmtSolver` relies on the underlying solver for term traversal and querying a term for the `Sort` or `Op`. If passed `true`, it instantiates a `LoggingSolver` wrapper which keeps track of the `Op`, `Sort` and children of terms as they are created. A `LoggingSolver` wraps all the terms and sorts created through the API. Thus, a `LoggingSolver` always returns a `LoggingTerm`. However, this is invisible to the user and all the objects can be used in the expected way. The logging feature is useful for solvers that alias sorts (for example don't distinguish between booleans and bitvectors of size one) or perform on-the-fly rewriting. The `LoggingSolver` wrapper ensures that the built term has the expected `Op`, `Sort` and children. In other words, the created term is exactly what was built through the API -- it cannot be rewritten or alias the sort. This drastically simplifies transferring between solvers and can be more intuitive than on-the-fly rewriting. Note: the rewriting still happens in the underlying solver, but this is hidden at the Smt-Switch level. Some solvers, such as `Yices2`, rely on the `LoggingSolver` for term traversal. E.g. creating a `Yices2` `SmtSolver` without term logging would not allow term traversal.

Here is an example that creates a solver interface to cvc5:
```
#include "smt-switch/cvc5_factory.h"

int main()
{
  // create a Cvc5Solver without logging
  smt::SmtSolver s = smt::Cvc5SolverFactory::create(false);
  return 0;
}

```

# Dependencies

Smt-Switch depends on the following libraries. Dependencies needed only for certain backends and/or optional features are marked \["optional" : _reason_\].
* CMake >= 3.1
* C compiler
* C++ compiler supporting C++11
* git
* curl \[optional : setup scripts in `contrib`\]
* Solver libraries
  * Bitwuzla (has setup script in `contrib`)
  * cvc5 (has setup script in `contrib`)
  * MathSAT (must be obtained independently; user responsible for meeting license conditions)
  * Yices2 (must be obtained independently; user responsible for meeting license conditions)
* pthread [optional: Bitwuzla]
* gmp [optional: cvc5, MathSAT, Yices2]
* autoconf [optional: Yices2 setup script]
* Java [optional: cvc5 ANTLR]
* Flex >= 2.6.4 [optional: SMT-LIB parser]
* Bison >= 3.7 [optional: SMT-LIB parser]
* Python [optional: Python bindings]
* Cython >= 0.29 [optional: Python bindings]
* [scikit-build](https://github.com/scikit-build/scikit-build/tree/master/skbuild) [optional: Python bindings]

# Operating Systems

Our `cmake` build system is currently only tested on Ubuntu Bionic and Mac OSX with XCode 12 but should work for other sufficiently modern (e.g. has C++11 support and CMake >= 3.1) Unix-based operating systems. Please file a GitHub issue if you have any problems!

# Solvers
To setup and install different solvers, first run the `./contrib/setup-<solver>.sh` script which builds position-independent static libraries in the `<solver>` directory. Then you can configure your `cmake` build with the `configure.sh` script. Enable a solver with `./configure.sh --<solver>`. By default only `libsmt-switch.so` is built without any solvers.

Some of the backend solvers have non-BSD compatible licenses. There are no provided setup scripts for these solvers. However, there are instructions for setting up these solvers in `./contrib`. Should you choose to link against these solver libraries, you assume all responsibility for meeting the license requirements of those libraries.

Once you've configured the build system, simply enter the build directory (`./build` by default) and run `make`. Each solver you add produces a `libsmt-switch-<solver>.so` shared object file. Running `make install` installs these libraries and the public header files into the configured prefix (`/usr/local` by default). Note that the header files are put in a directory, e.g. `/usr/local/include/smt-switch`.

## Currently Supported Solvers

### BSD compatible

* Bitwuzla
* Bitwuzla
* cvc5
* Z3

### Non-BSD compatible

* MathSAT
* Yices2

## Custom Solver Location
If you'd like to try your own version of a solver, you can use the `configure.sh` script to point to your custom location with `--<solver>-home`. You will need to build static libraries (.a) and have them be accessible in the standard location for that solver. For example, you would point to a custom location of cvc5 like so:
`./configure.sh --prefix=<your desired install location> --cvc5-home ./custom-cvc5`

where `./custom-cvc5/build/src/libcvc5.a` and `./custom-cvc5/build/src/parser/libcvc5parser.a` already exist. `build` is the default build directory for `cvc5`, and thus that's where `cmake` is configured to look.

# Building Tests
You can run all tests for the currently built solvers with `make test` from the build directory. To run a single test, run the binary `./tests/<test name>`. After you have a full installation, you can build the tests yourself by updating the includes to include the `smt-switch` directory. For example: `#include "cvc5_factory.h"` -> `#include "smt-switch/cvc5_factory.h"`.

## Debug
The tests currently use C-style assertions which are compiled out in Release mode (the default). To build tests with assertions, please add the `--debug` flag when using `./configure.sh`.

# Python bindings
It is highly recommended to use a Python [virtual environment](https://docs.python.org/3/library/venv.html) or [Conda environment](https://docs.conda.io/en/latest/) when building Python bindings. Note: only Python3 is supported.

First, install the required Python modules:
```
python3 -m pip install scikit-build Cython pytest
```
If you're building the python bindings in a setting where you don't care too much about runtime speed (e.g. for CI), you can add the option `--install-option="--no-cython-compile"` to the end of the Cython installation command to install it faster.

Then, to compile python bindings, use the `--python` flag of `configure.sh`. After configuring with python bindings, run `make` in the build directory as usual. The Python extension module will be `build/python/smt_switch/smt_switch*.so`. To install this in your python environment, you can run `python3 -m pip install -e ./python` from the `build` directory.

After installing the bindings, you can test them from the top-level of the repository with:
```
pytest ./tests/
```

## PySMT front end
Optionally, smt-switch can be used with a [pySMT](https://pysmt.readthedocs.io/en/latest/) front-end .  To install the pySMT front-end install `smt-switch` with the `pysmt` extra (`python3 -m install -e ./python[pysmt]`).  Note, some shells, notable `zsh`, require brackets be escaped or the path to be quoted, i.e., `./python\[pysmt\]` or `"./python[pysmt]"`.

A pySMT solver for each switch back-end can be instantiated directly or using the helper function `Solver`:
```Python
from smt_switch import pysmt_frontend

# direct instantiation must pass an enviroment and a logic
solver = pysmt_frontend.SwitchCvc5(ENV, LOGIC)

# with the helper function will try to use a general logic
solver = pysmt_frontend.Solver("cvc5")

# with the helper function will use the specified logic
solver = pysmt_frontend.Solver("cvc5", LOGIC)

# Note a solver can be used as a context manager:
with pysmt_frontend.Solver("cvc5") as solver: ...
```

Please refer to the pySMT docs for further information.


## Testing python bindings
Python bindings are tested with [pytest](https://docs.pytest.org/en/latest/). This can be installed using `pip` or automatically by installing the python bindings with the `test` extra (`python3 -m install -e ./python[test]`). To run all tests, simply run `pytest ./tests` from the top-level directory. Note, running `pytest` alone might unnecessarily run tests in dependencies located in subdirectories. To run a particular test, use the `-k test_name[parameter1-...-parameter_n]` format, e.g. `pytest -k test_bvadd[create_btor_solver]`.  The tests for the pySMT front-end will only be run if it is installed.  Note, multiple extras may be installed by passing them as a comma separated list:`python3 -m install -e ./python[test,pysmt]`.

# Current Limitations and Gotchas
While we try to guarantee that all solver backends are fully compliant with the abstract interface, and exhibit the exact same behavior given the same API calls, we are not able to do this in every case (yet). Below are some known, current limitations along with recommended usage.

* **Undefined behavior.** Sharing terms between different solver instances will result in undefined behavior. This is because we use a static cast to recover the backend solver implementation from an abstract object. To move terms between solver instances, you can use a `TermTranslator` which will rebuild the term in another solver. A given `TermTranslator` object can only translate terms from **one** solver to **one** new one. If some symbols have already been created in the new solver, you can populate the `TermTranslator`'s cache so that it knows which symbols correspond to each other
* Bitwuzla's `substitute` implementation does not work for formulas containing uninterpreted functions. To get around this, you can use a LoggingSolver. See below.
* Bitwuzla does not support `reset_assertions` yet. You can however simulate this by setting the option "base-context-1" to "true". Under the hood, this will do all solving starting at context 1 instead of 0. This will allow you to call `reset_assertions` just like for any other solver.
* The Z3 backend has not implemented term iteration (getting children) yet, but that should be added soon.
* Datatypes are currently only supported in cvc5

## Recommended usage

### Logging solvers

A `LoggingSolver` is a wrapper around another `SmtSolver` that keeps track of Term DAGs at the smt-switch level. This guarantees that if you create a term and query it for its sort, op, and children, it will give you back the exact same objects you built it with. Without the `LoggingSolver` wrapper, this is not guaranteed for all solvers. This is because some solvers perform on-the-fly rewriting and/or alias sorts (e.g. treat `BOOL` and `BV` of size one equivalently). Below, we give some recommendations for when to use a `LoggingSolver` for different backends. To use a `LoggingSolver`, pass `true` to the `create` function when instantiating a solver.

* Bitwuzla
  * Use a `LoggingSolver` when you want to avoid issues with sort aliasing between booleans and bit-vectors of size one and/or if you'd like to ensure that a term's children are exactly what were used to create it. Bitwuzla performs very smart on-the-fly rewriting. Additionally, use a `LoggingSolver` if you will need to use the `substitute` method on formulas that contain uninterpreted functions.
* cvc5
  * cvc5 does not alias sorts or perform on-the-fly rewriting. Thus, there should never be any reason to use a `LoggingSolver`.
* MathSAT
  * Use a `LoggingSolver` only if you want to guarantee that a term's Op and children are exactly what you used to create it. Without a `LoggingSolver`, MathSAT will perform _very_ light rewriting.
* Yices2
  * Use a `LoggingSolver` if you need term iteration
  * Yices2 has a different term representation under the hood which cannot easily be converted back to SMT-LIB. Thus, term traversal is currently only supported through a `LoggingSolver`.

## Contributions

We welcome external contributions, please see
[CONTRIBUTING.md](./CONTRIBUTING.md) for more details. If you are interested in
becoming a long-term contributor to smt-switch, please contact one of the
primary authors in [AUTHORS](./AUTHORS)
