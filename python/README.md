# smt-switch

Python bindings for
[smt-switch](https://github.com/stanford-centaur/smt-switch), a generic C++ API
for SMT solving. It provides a single abstract interface that several SMT
solvers implement, so you can write solver-agnostic code and switch back ends
without rewriting it.

## Installation

```sh
python3 -m pip install smt-switch
```

The published wheels bundle the solver back ends with permissive licenses:
[Bitwuzla](https://bitwuzla.github.io/), [cvc5](https://cvc5.github.io/), and
[Z3](https://github.com/Z3Prover/z3). Boolector, MathSAT, and Yices 2 are
supported by smt-switch but are not included in the wheels; to use those, build
from source as described in the
[main README](https://github.com/stanford-centaur/smt-switch#python-bindings).

Two optional extras are available: `smt-switch[pysmt]` installs the
[pySMT](https://pysmt.readthedocs.io/en/latest/) front end, and
`smt-switch[test]` installs [pytest](https://docs.pytest.org/en/latest/) for
running the test suite.

## Usage

Every back end is created through the same factory interface and driven through
the same solver object:

```python
import smt_switch as ss

solver = ss.create_cvc5_solver(logging=False)
solver.set_opt("produce-models", "true")

bv8 = solver.make_sort(ss.sortkinds.BV, 8)
x = solver.make_symbol("x", bv8)
y = solver.make_symbol("y", bv8)

# x + y == 10 and x != 0
solver.assert_formula(
    solver.make_term(
        ss.primops.Equal,
        solver.make_term(ss.primops.BVAdd, x, y),
        solver.make_term(10, bv8),
    )
)
solver.assert_formula(
    solver.make_term(ss.primops.Distinct, x, solver.make_term(0, bv8))
)

result = solver.check_sat()
if result.is_sat():
    print("x =", int(solver.get_value(x)))
    print("y =", int(solver.get_value(y)))
```

The back ends compiled into your installation are available in the
`smt_switch.solvers` dictionary, which maps a name such as `"cvc5"` to its
factory function. This is the easiest way to run the same code across every
available solver:

```python
import smt_switch as ss

for name, create_solver in ss.solvers.items():
    solver = create_solver(logging=False)
    ...
```

## Documentation and support

Further documentation, the C++ API, build instructions for the other solver back
ends, and known limitations are in the
[main repository](https://github.com/stanford-centaur/smt-switch). Please report
problems on the
[issue tracker](https://github.com/stanford-centaur/smt-switch/issues).

## License

smt-switch is distributed under the BSD 3-Clause license. Note that the solver
back ends carry their own licenses. See
[LICENSE](https://github.com/stanford-centaur/smt-switch/blob/main/LICENSE) for
details.
