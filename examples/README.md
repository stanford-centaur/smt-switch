# Examples

This directory contains example usage of smt-switch.

## QF_UFBV
`QF_UFBV` stands for Quantifier-free uninterpreted functions and bit-vectors. The files `cvc4_qf_ufbv.cpp` and `btor_qf_ufbv.cpp` demonstrate some common usage of the API with this logic. The `build.sh` script will setup and install smt-switch in this directory and then build the examples. The script has comments explaining each step for building smt-switch. This assumes that you have all the necessary dependencies other than the underlying solvers and smt-switch already installed.  You can look at the `Makefile` to understand how to link smt-switch to a binary. If the script succeeds in building everything, you can run each of the files with `./cvc4_qf_ufbv.out` and `./btor_qf_ufbv.out`, respectively. Note that there may be a delay for looking up the shared libraries on some systems the first time they are run. Importantly, notice that the files differ by only two lines, demonstrating that changing the solver is straightforward.
