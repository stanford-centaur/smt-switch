#!/bin/bash

cd ../tests/unit/
make clean
make sort
./unit-sort.out
make exceptions
./unit-exceptions.out
make func
./unit-func.out
make clean

cd ../btor/
make clean
make BTOR_HOME="../../boolector"
./btor-tests.out
