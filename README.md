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

A `Term` or `Sort` keeps alive the backend state it points into, so it can still
be used after the `SmtSolver` that created it is destroyed.

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
#include <smt-switch/cvc5_factory.h>

int main()
{
  // create a Cvc5Solver without logging
  smt::SmtSolver s = smt::Cvc5SolverFactory::create(false);
  return 0;
}

```

To choose the solver at run time instead, `smt-switch/solver_factory.h` creates
one from its `SolverEnum`. It reaches any backend the program links, or one
installed beside `libsmt-switch`, so linking `SmtSwitch::smt-switch` alone is
enough:

```cpp
#include <smt-switch/solver_factory.h>

int main()
{
  for (smt::SolverEnum se : smt::available_solver_enums())
  {
    smt::SmtSolver s = smt::create_solver(se, /* logging */ false);
  }
  return 0;
}

```

## Dependencies

- CMake >= 3.16
- GNU Make or Ninja
- C compiler
- C++ compiler supporting C++17

## Operating Systems

We officially support the latest Ubuntu LTS on 64-bit Intel and AMD CPUs and the
latest macOS on Apple silicon. Other GNU/Linux distributions should work as
well, although we do no testing on them. The BSDs and other Unix-like systems
are not supported yet: several of the solver builds run `make` and need GNU
make, which those systems install under another name. Please file a GitHub issue
if you have any problems!

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

To use the pinned version even when another one is installed, pass
`--no-system-<solver>` (or `--no-system-bison` for the SMT-LIB reader's parser
generator): the copy under `deps/` is then used, and downloaded first if it is
not there yet. This cannot be combined with that solver's `--<solver>-dir` or
with `--no-auto-deps`, and Yices2 still needs `--allow-gpl`.

Each enabled solver produces a `libsmt-switch-<solver>.so`.
`cmake --install build` installs those and the public headers under the
configured prefix (`/usr/local` by default), with the headers in a subdirectory
of their own, e.g. `/usr/local/include/smt-switch`. The installed CMake package
remembers the prefix of each solver found under `deps/` or a `--<solver>-dir`,
so `find_package(SmtSwitch COMPONENTS <solver>)` finds that solver without its
location being given again; setting `<Package>_ROOT`, e.g. `cvc5_ROOT`,
overrides it.

Each solver is listed below with the libraries it needs beyond the core
dependencies. These must be installed on the system already if the solvers are
built automatically by smt-switch.

### Permissively Licensed (BSD Compatible)

- **Bitwuzla** — Meson, GMP, MPFR
- **Boolector**
- **cvc5** — GMP
- **Z3** — CMake >= 3.26, GMP and its C++ bindings

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
unpacked into `deps/mathsat` (or specify `--mathsat-dir`, see below).

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

A relative path is taken from the directory `configure.sh` is run in. A
`--<solver>-dir` has to hold the solver: if the directory does not exist or the
solver is not installed there, configuration stops rather than use another copy
or build one. The same goes for `--bison-dir`.

Boolector is the exception that also needs its sources. Smt-switch needs access
to Boolector's private headers to support term iteration, so
`--boolector-src-dir` points at the source tree alongside `--boolector-dir`. It
defaults to `<boolector-dir>/src/boolector`.

### Supported Versions

Configuration stops if a solver is older than the oldest version below. The
newest tested version is the newest release smt-switch was tested with; newer
ones may work too. What is built automatically is pinned in
`cmake/provision/<solver>/pin.cmake`.

| Solver    | Oldest | Newest tested |
| --------- | ------ | ------------- |
| Bitwuzla  | 0.4.0  | 0.9.1         |
| Boolector | 3.2.2  | 3.2.4         |
| cvc5      | 1.4.0  | 1.4.2         |
| MathSAT   | 5.6.12 | 5.6.20        |
| Yices2    | 2.7.0  | 2.7.0         |
| Z3        | 4.12.2 | 5.4.1         |

- Bitwuzla interpolates only from 0.9.0 on, and 0.9.0 and 0.9.1 answer `unknown`
  to some equalities with a constant array.
- A Yices2 2.7.0 built with `--enable-thread-safety` hangs in
  `check_sat_assuming` when the answer is sat.
- Some older executables are not compliant with SMT-LIB, so the generic solver
  fails with them where linking against the same release works: Boolector 3.2.2
  prints Boolean values as bit-vectors.

### Static Linking

It is possible to produce smt-switch libraries (`libsmt-switch.a`, etc.) instead
of the default shared objects by passing `--static` to `configure.sh`. This can
be useful, for example, for producing self-contained binaries that need to be
uploaded to a shared computing cluster.

## SMT-LIB reader

`SmtLibReader` parses an SMT-LIB 2 script and issues its commands against a
solver, so a benchmark file can drive any backend through the same interface as
the C++ API. Its interface is in `smt-switch/smtlib_reader.h`, and it is a
library of its own, `smt-switch-smtlib`, which the CMake package provides as the
`smtlib` component. It can be enabled by passing `--smtlib-reader` to
`configure.sh`. It needs:

- flex >= 2.6.4
- Bison >= 3.7 (will be downloaded automatically if no new enough one is found;
  on macOS, `brew install bison` is enough)

## Building Tests

Testing needs GTest >= 1.14, which is downloaded and built automatically if no
appropriate installation is found. Invoking CTest as shown in Quick Start will
run every test. Individual test suites can be run using `./build/tests/<suite>`.

## Python bindings

It is highly recommended to use a Python
[virtual environment](https://docs.python.org/3/library/venv.html) or
[Conda environment](https://docs.conda.io/en/latest/) when building Python
bindings. Note: only Python 3.10 or later is supported.

First, install Cython, which the build needs:

```sh
python3 -m pip install Cython
```

Then, to compile Python bindings, use the `--python` flag of `configure.sh`,
which needs CMake 3.18 or newer. Afterwards, build `smt-switch` as usual and
install it. The bindings go into the `site-packages` directory of the Python
that `configure.sh` found, which is the active environment's:

```sh
cmake --install build
```

To install only the bindings, add `--component python`. A shared build puts the
smt-switch libraries they load into the package as well.

Alternatively, `python3 -m pip install .` from the root of the repository builds
and installs a wheel with Bitwuzla, cvc5 and Z3, the solvers the wheels on PyPI
bundle.

The Python bindings can be tested by installing `pytest` and running it from the
`tests/python` directory. To run a particular test, use the
`-k test_name[parameter1-...-parameter_n]` format, e.g.:

```sh
pytest -k test_bvadd[create_btor_solver]
```

### PySMT front end

Optionally, smt-switch can be used with a
[pySMT](https://pysmt.readthedocs.io/en/latest/) front end, by installing pySMT
beside it (a wheel from PyPI takes the `pysmt` extra, `smt-switch[pysmt]`):

```sh
python3 -m pip install pysmt
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

When pySMT is installed, tests specific to the front end are also included in
the Python test suites.

## Exceptions

Every exception smt-switch throws derives from `smt::Exception`, which derives
from `std::exception`. Each subclass names a cause, the same on every backend:

- `smt::IncorrectUsageException`: the caller asked for something SMT-LIB, or the
  solver's documented contract for an extension, does not allow, such as a term
  of the wrong sort or a model after an unsat check.
- `smt::ParseException`, an `IncorrectUsageException`: the SMT-LIB reader cannot
  parse its input. The message starts with the location.
- `smt::NotImplementedException`: the request is allowed, but the solver or its
  backend cannot carry it out, such as an option it does not know or a theory it
  lacks.
- `smt::SolverException`: the solver itself failed, for instance at an internal
  limit.
- `smt::SystemException`: the operating system refused a call, such as opening a
  file or starting a process.
- `smt::InternalException`: smt-switch reached a state its own code should rule
  out, which is a bug to report.

## Current Limitations

Every backend implements the same interface, but not every solver supports every
theory or feature. A backend refuses what its solver cannot do with
`NotImplementedException`, and a misuse with `IncorrectUsageException`, as
[Exceptions](#exceptions) describes.

### Supported features

A dash marks a feature the solver lacks; "not yet" marks one the solver has but
smt-switch does not support yet.

<!-- A table row cannot wrap, so the line length limit is off here. -->

<!-- markdownlint-disable MD013 -->

| Feature                        | Boolector | Bitwuzla | cvc5    | MathSAT | Yices2  | Z3      |
| ------------------------------ | --------- | -------- | ------- | ------- | ------- | ------- |
| Bit-vectors, arrays            | yes       | yes      | yes     | yes     | yes     | yes     |
| Bit-vector overflow predicates | not yet   | not yet  | not yet | not yet | not yet | not yet |
| Ints and Reals                 | —         | —        | yes     | yes     | yes     | yes     |
| Floating point                 | —         | not yet  | not yet | not yet | —       | not yet |
| Strings                        | —         | —        | yes     | —       | —       | not yet |
| Datatypes                      | —         | —        | yes     | —       | —       | yes     |
| Quantifiers                    | yes       | yes      | yes     | —       | —       | yes     |
| Uninterpreted sorts            | —         | yes (1)  | yes     | yes     | yes     | yes     |
| Unsat cores                    | yes       | yes      | yes     | yes     | yes     | yes     |
| Interpolation                  | —         | yes (2)  | yes     | yes     | yes (3) | —       |
| Time limits                    | yes       | yes      | yes     | yes     | yes     | yes     |

<!-- markdownlint-enable MD013 -->

- (1) Bitwuzla answers `unknown` to an equality between two terms of an
  uninterpreted sort that its preprocessing cannot remove.
- (2) From Bitwuzla 0.9.0.
- (3) With Yices2 built with MCSAT.

The generic solver drives a solver executable over SMT-LIB, and supports what
that executable does, except interpolation.

### Differences between backends

- **Terms belong to their solver.** A solver refuses terms and sorts made by
  another one with `IncorrectUsageException`; only Yices2, which keeps one term
  table per process, accepts another Yices2 solver's. A `TermTranslator`
  rebuilds terms in another solver. Each one translates from **one** solver to
  **one** other, and if some symbols already exist in the target solver, its
  cache must be populated so that it knows which symbols correspond.
- **Powers.** `Pow` is SMT-LIB's `**`. cvc5, MathSAT and Yices2 accept only a
  constant exponent from 0 (Yices2 up to 2^32 − 1); Z3 accepts any. The generic
  solver sends a power to a constant exponent as products and comparisons, which
  every executable reads, and any other as `**`, which only Z3 5.4 and newer
  read.
- **Boolector's `reset_assertions`** needs the option `base-context-1` set to
  `true`, which does all solving at context 1 instead of 0. The hidden context
  is not counted: `get_context_level` still starts at 0.

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
the `create` function when instantiating a solver. Bitwuzla, cvc5 and Z3 never
need one.

- Boolector
  - Use a `LoggingSolver` to avoid issues with sort aliasing between booleans
    and bit-vectors of size one and to ensure that a term's children are exactly
    what were used to create it. Boolector performs very smart on-the-fly
    rewriting.
- MathSAT
  - Use a `LoggingSolver` to guarantee that a term's Op and children are always
    exactly what were used to create it. Without a `LoggingSolver`, MathSAT will
    perform very light rewriting.
- Yices2
  - Use a `LoggingSolver` to guarantee that a term's Op and children are always
    exactly what were used to create it. Without one, iteration walks Yices2's
    own term representation: a sum or product is read back from a polynomial,
    and a term bridging booleans and bit-vectors of size one is read back as an
    `Equal`, `Concat` or `Ite` over children built for the purpose. These
    children rebuild an equivalent term, but not necessarily the same one.

## Contributions

We welcome external contributions, please see
[CONTRIBUTING.md](./CONTRIBUTING.md) for more details. If you are interested in
becoming a long-term contributor to smt-switch, please contact one of the
primary authors in [AUTHORS](./AUTHORS). For development instructions and
guidelines, see the [DEVELOPERS doc](./DEVELOPERS.md).
