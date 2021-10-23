# Examples

This directory contains example usage of smt-switch.

## QF_UFBV
`QF_UFBV` stands for quantifier-free uninterpreted functions and bit-vectors.
The files [cvc5_qf_ufbv.cpp](cvc5_qf_ufbv.cpp) and
[btor_qf_ufbv.cpp](btor_qf_ufbv.cpp) demonstrate some common usage of the API
with this logic.

The `build.sh` script will setup and install smt-switch in this directory and
then build the examples. The script has comments explaining each step for
building smt-switch. The script assumes you already have dependencies installed
and that boolector and cvc5 have been built in the top-level repository under
`deps/CVC5` and `deps/boolector`. You can use the helper scripts
[setup-cvc5.sh](../contrib/setup-cvc5.sh) and
[setup-btor.sh](../contrib/setup-btor.sh) to automate this. If the build script
fails and you haven't recently installed the solvers, you might have an old
version. You can try deleting them from `deps` and rebuilding them.

You can look at the `Makefile` to understand how to link smt-switch to a binary.
If the script succeeds in building everything, you can run each of the files
with `./cvc5_qf_ufbv.out` and `./btor_qf_ufbv.out`, respectively. Note that
there may be a delay for looking up the shared libraries on some systems the
first time they are run. Importantly, notice that the files differ by only two
lines of code (excluding comments), demonstrating that changing the solver is
straightforward.

To explore the API, you can change either of those files and run `make` again.
To remove the built binaries, run `make clean`. To clean up all the build and
install files for `smt-switch` in this directory, run `make clean-all`.

## Python bindings
You can also run the same example through the Python bindings with the file,
[python_qf_ufbv.py](python_qf_ufbv.py). This requires building the Python
bindings, which can be done by running `./build.sh --python`. If you have
already built without Python bindings, please run `make clean-all` before
rebuilding. `Python3` along with the modules `Cython` and `pytest` are required
for building the bindings and running the example. It is recommended to use a
`Python3` [virtual environment](https://docs.python.org/3/library/venv.html).
