CVC4_HOME="./CVC4"
GENERIC_SRC="../../src"
SOURCE=$(GENERIC_SRC)/sort.cpp $(GENERIC_SRC)/ops.cpp $(GENERIC_SRC)/term.cpp  ../../cvc4/src/cvc4_fun.cpp ../../cvc4/src/cvc4_sort.cpp ../../cvc4/src/cvc4_term.cpp ../../cvc4/src/cvc4_solver.cpp ../../cvc4/src/cvc4_factory.cpp
CXXFLAGS=-no-pie

all: cvc4_test.out

debug: all
debug: DEBUG=-g -D_DEBUG

# After install
cvc4_test.out: cvc4_test.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I/usr/local/include/smt-switch -o cvc4_test.out cvc4_test.cpp -lsmt-switch -lsmt-switch-cvc4

clean:
	rm -rf *.out
