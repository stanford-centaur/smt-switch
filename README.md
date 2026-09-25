# Smt-Switch

A generic C++ API for SMT solving. It provides abstract classes which can be
implemented by different SMT solvers.

## Quick Start

```sh
./configure.sh --<solver1> --<solver2>
cd build
cmake --build .
ctest
```

The available solvers and their specific dependencies are described in the
Solvers section below.

For an example of how to link and use `smt-switch`, please see the
[examples directory](./examples).

## Architecture Overview

There are three abstract classes:

- `AbsSmtSolver`
- `AbsSort`
- `AbsTerm`

Each of them has a `using` statement that names a smart pointer of that type,
e.g. `using Term = shared_ptr<AbsTerm>;`. The key thing to remember when using
this library is that all solver-specific objects are pointers to the abstract
base class. `SmtSolver`, `Sort`, and `Term` are all smart pointers. Note: there
are many convenience functions which operate on these pointers, so they may not
*look* like pointers. Additionally, the library also includes `using` statements
for commonly used data structures, for example, `TermVec` is a vector of shared
pointers to `AbsTerm`s.

The function names are based on SMT-LIB. The general rule is that
functions/methods in this library can be obtained syntactically from SMT-LIB
commands by replacing dashes with underscores. There are a few exceptions, for
example `assert` is `assert_formula` in this library to avoid clashing with the
`assert` macro. Operator names are also based on SMT-LIB operators, and can be
obtained syntactically from an SMT-LIB operator by capitalizing the first letter
and any letter after an underscore. The only exception is `bv` which is always
capitalized to `BV` and does not count towards the capitalization of the first
letter. Some examples include:

- `And`
- `BVAnd`
- `Zero_Extend`
- `BVAshr`

Please see this [extended abstract](https://arxiv.org/abs/2007.01374) for more
documentation or the `tests` directory for some example usage.

## Creating a Smt-Switch Solver

To create a Smt-Switch solver through the API, first include the relevant
factory header and then use the static `create` method. It takes a single
boolean parameter which configures term logging. If passed `false`, the created
`SmtSolver` relies on the underlying solver for term traversal and querying a
term for the `Sort` or `Op`. If passed `true`, it instantiates a `LoggingSolver`
wrapper which keeps track of the `Op`, `Sort` and children of terms as they are
created. A `LoggingSolver` wraps all the terms and sorts created through the
API. Thus, a `LoggingSolver` always returns a `LoggingTerm`. However, this is
invisible to the user and all the objects can be used in the expected way. The
logging feature is useful for solvers that alias sorts (for example don't
distinguish between booleans and bitvectors of size one) or perform on-the-fly
rewriting. The `LoggingSolver` wrapper ensures that the built term has the
expected `Op`, `Sort` and children. In other words, the created term is exactly
what was built through the API -- it cannot be rewritten or alias the sort. This
drastically simplifies transferring between solvers and can be more intuitive
than on-the-fly rewriting. Note: the rewriting still happens in the underlying
solver, but this is hidden at the Smt-Switch level. Some solvers, such as
`Yices2`, rely on the `LoggingSolver` for term traversal. E.g. creating a
`Yices2` `SmtSolver` without term logging would not allow term traversal.

Here is an example that creates a solver interface to cvc5:

```cpp
#include "smt-switch/cvc5_factory.h"

int main()
{
  // create a Cvc5Solver without logging
  smt::SmtSolver s = smt::Cvc5SolverFactory::create(false);
  return 0;
}

```

## Dependencies

- CMake >= 3.14
- GNU Make or Ninja
- C compiler
- C++ compiler supporting C++17

## Operating Systems

We officially support the latest Ubuntu LTS on 64-bit Intel and AMD CPUs and the
latest macOS on Apple silicon. Other Unix-like systems should work as well;
other GNU/Linux distributions certainly do, and the BSDs ought to, although we
do no testing on either. Please file a GitHub issue if you have any problems!

## Solvers

Enable a solver by passing its `--<solver>` flag to `configure.sh`. By default
only `libsmt-switch.so` is built, with no solvers at all.

A solver that cannot be found is downloaded and built automatically (with the
exceptions described below), as a position-independent static library with its
own prefix under `deps/`: the sources are unpacked into
`deps/<solver>/src/<solver>` and the build is installed into `deps/<solver>`.
Pass `--no-auto-deps` to turn that off and be told what is missing instead.
Nothing is downloaded for a solver that is already installed, so the
`--<solver>-dir` flags below take precedence.

Each enabled solver produces a `libsmt-switch-<solver>.so`.
`cmake --install build` installs those and the public headers under the
configured prefix (`/usr/local` by default), with the headers in a subdirectory
of their own, e.g. `/usr/local/include/smt-switch`.

Each solver is listed below with the libraries it needs beyond the core
dependencies. These must be installed on the system already if the solvers are
built automatically by smt-switch.

### Permissively Licensed (BSD Compatible)

- **Bitwuzla** — Meson, GMP, MPFR
- **Boolector**
- **cvc5** — GMP
- **Z3** — GMP and its C++ bindings

### Licensed under the GPL

- **Yices2** — Autoconf, gperf, GMP

Yices2 is under the GPLv3, so linking against it puts the whole smt-switch build
under the GPLv3 as well. Automatically downloading it needs to be explicitly
enabled with `--allow-gpl`.

### Custom License

- **MathSAT** — GMP

MathSAT is under a custom license, and linking against it changes the license of
the smt-switch build. It will therefore not be automatically downloaded and must
be obtained independently from <https://mathsat.fbk.eu/download.html> and
unpacked into `deps/mathsat` (or specify `--msat-dir`, see below).

### Custom Solver Location

It is possible to use a custom (externally-provided) version of a solver by
passing `--<solver>-dir` to `configure.sh`. These options take **install
prefixes**, not source trees: the directory a solver was installed into, holding
`include/` and `lib/`. For example:

```sh
./configure.sh --cvc5-dir=/home/user/local
```

where `/home/user/local/lib/libcvc5.a` and `/home/user/local/lib/cmake/cvc5/`
already exist, which is what `cmake --install` produces. Each solver is located
with `find_package`, so a solver installed somewhere `cmake` already searches —
a distribution package, for instance — is picked up without any flag at all.

Boolector is the exception that also needs its sources. Smt-switch needs access
to Boolector's private headers to support term iteration, so `--btor-src-dir`
points at the source tree alongside `--btor-dir`. It defaults to
`<btor-dir>/src/boolector`.

### Static Linking

It is possible to produce smt-switch libraries (`libsmt-switch.a`, etc.) instead
of the default shared objects by passing `--static` to `configure.sh`. This can
be useful, for example, for producing self-contained binaries that need to be
uploaded to a shared computing cluster.

## SMT-LIB reader

`SmtLibReader` parses an SMT-LIB 2 script and issues its commands against a
solver, so a benchmark file can drive any backend through the same interface as
the C++ API. Its interface is in `smt-switch/smtlib_reader.h`. It can be enabled
by passing `--smtlib-reader` to `configure.sh`. It needs:

- flex >= 2.6.4
- Bison >= 3.7 (will be downloaded automatically if no new enough one is found)

## Building Tests

Testing needs GTest >= 1.14, which is downloaded and built automatically if no
appropriate installation is found. Invoking CTest as shown in Quick Start will
run every test. Individual test suites can be run using `./build/tests/<suite>`.

Some tests currently use C-style assertions which are compiled out in release
mode (the default). To build tests with assertions, pass
`-DCMAKE_BUILD_TYPE=Debug` to `./configure.sh`, or see
[DEVELOPERS.md](./DEVELOPERS.md#debug-builds) for building release and debug
side by side.

## Python bindings

It is highly recommended to use a Python
[virtual environment](https://docs.python.org/3/library/venv.html) or
[Conda environment](https://docs.conda.io/en/latest/) when building Python
bindings. Note: only Python 3.10 or later is supported.

First, install the packages the build needs:

```sh
python3 -m pip install Cython packaging setuptools
```

Then, to compile Python bindings, use the `--python` flag of `configure.sh`.
Afterwards, build `smt-switch` as usual. The Python wheel will be built inside
`build/python` as the file `smt_switch-<version>-<tags>.whl`. This can be
installed with `pip`:

```sh
python3 -m pip install build/python/<filename>.whl
```

The Python bindings can be tested by installing the wheel with the test extra,
`build/python/<filename>.whl[test]`, and running `pytest` from the
`tests/python` directory. Note that some shells, like `zsh`, require brackets to
be escaped or the path to be quoted, i.e., `build/python/<filename>.whl\[test\]`
or `"build/python/<filename>.whl[test]"`. To run a particular test, use the
`-k test_name[parameter1-...-parameter_n]` format, e.g.:

```sh
pytest -k test_bvadd[create_btor_solver]
```

### PySMT front end

Optionally, smt-switch can be used with a
[pySMT](https://pysmt.readthedocs.io/en/latest/) front end using the `pysmt`
extra:

```sh
python3 -m pip install build/python/<filename>.whl[pysmt]
```

A pySMT solver for each switch back-end can be instantiated directly or using
the helper function `Solver`:

```Python
from smt_switch import pysmt_frontend

# direct instantiation must pass an environment and a logic
solver = pysmt_frontend.SwitchCvc5(ENV, LOGIC)

# with the helper function will try to use a general logic
solver = pysmt_frontend.Solver("cvc5")

# with the helper function will use the specified logic
solver = pysmt_frontend.Solver("cvc5", LOGIC)

# Note a solver can be used as a context manager:
with pysmt_frontend.Solver("cvc5") as solver:
    ...
```

Please refer to the pySMT docs for further information.

When the pySMT frontend is installed, tests specific to it will also be included
in the Python test suites. Note, multiple extras may be installed by passing
them as a comma-separated list:

```sh
python3 -m pip install build/python/<filename>.whl[test,pysmt]
```

## Current Limitations

While we try to guarantee that all solver backends are fully compliant with the
abstract interface, and exhibit the exact same behavior given the same API
calls, we are not able to do this in every case (yet). Below are some known,
current limitations along with recommended usage.

- **Undefined behavior.** Sharing terms between different solver instances will
  result in undefined behavior. This is because we use a static cast to recover
  the backend solver implementation from an abstract object. To move terms
  between solver instances, a `TermTranslator` can be used. This will rebuild
  the term in another solver. A given `TermTranslator` object can only translate
  terms from **one** solver to **one** new one. If some symbols have already
  been created in the new solver, the `TermTranslator`'s cache needs to be
  populated, so that it knows which symbols correspond to each other
- Boolector's `substitute` implementation does not work for formulas containing
  uninterpreted functions. To get around this, a LoggingSolver can be used, see
  below.
- Boolector does not support `reset_assertions`. Smt-switch can simulate this
  when the option "base-context-1" is set to "true". Under the hood, this will
  do all solving starting at context 1 instead of 0. This will enable calling
  `reset_assertions` just like for any other solver.
- The Z3 backend does not support term iteration over quantified expressions,
  though it does for every other kind of term.
- Datatypes are currently only supported in cvc5

### Recommended usage

#### Logging solvers

A `LoggingSolver` is a wrapper around another `SmtSolver` that keeps track of
Term DAGs at the smt-switch level. This guarantees that if a term is created, it
will give back the exact same objects when queried for its sort, op, and
children as it was created with. Without the `LoggingSolver` wrapper, this is
not guaranteed for all solvers. This is because some solvers perform on-the-fly
rewriting and/or alias sorts (e.g. treat `BOOL` and `BV` of size one
equivalently). Below, we give some recommendations for when to use a
`LoggingSolver` for different backends. To use a `LoggingSolver`, pass `true` to
the `create` function when instantiating a solver. Bitwuzla, cvc5, and Z3 should
never necessitate the use of a `LoggingSolver`.

- Boolector
  - Use a `LoggingSolver` to avoid issues with sort aliasing between booleans
    and bit-vectors of size one and to ensure that a term's children are exactly
    what were used to create it. Boolector performs very smart on-the-fly
    rewriting. Additionally, using the `substitute` method on formulas that
    contain uninterpreted functions is only supported when using a
    `LoggingSolver`.
- MathSAT
  - Use a `LoggingSolver` to guarantee that a term's Op and children are always
    exactly what were used to create it. Without a `LoggingSolver`, MathSAT will
    perform very light rewriting.
- Yices2
  - Use a `LoggingSolver` for term iteration support. Yices2 has a different
    term representation under the hood which cannot easily be converted back to
    SMT-LIB. Thus, term traversal is only supported through a `LoggingSolver`.

## Contributions

We welcome external contributions, please see
[CONTRIBUTING.md](./CONTRIBUTING.md) for more details. If you are interested in
becoming a long-term contributor to smt-switch, please contact one of the
primary authors in [AUTHORS](./AUTHORS). For development instructions and
guidelines, see the [DEVELOPERS doc](./DEVELOPERS.md).
