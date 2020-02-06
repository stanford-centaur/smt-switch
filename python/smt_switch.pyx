# distutils: language = c++
# distutils: include_dirs = ../ ../btor/
# distutils: library_dirs = ../build/ ../build/btor/
# distutils: extra_compile_args = -std=c++17
# distutils: libraries = smt-switch smt-switch-msat smt-switch-btor

include "enums.pxi"
include "smt_switch_imp.pxi"
