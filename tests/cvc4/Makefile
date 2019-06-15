CVC4_HOME="./CVC4"
GENERIC_SRC="../../src"
SOURCE=$(GENERIC_SRC)/sort.cpp $(GENERIC_SRC)/ops.cpp $(GENERIC_SRC)/term.cpp ../../cvc4/src/cvc4_term.cpp ../../cvc4/src/cvc4_sort.cpp
CXXFLAGS=-no-pie

all: cvc4_test.out

debug: all
debug: DEBUG=-g -D_DEBUG

cvc4_test.out: cvc4_test.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include -I../../src/ -I../../cvc4/include -I$(CVC4_HOME)/src -I$(CVC4_HOME)/src/include -o cvc4_test.out cvc4_test.cpp $(SOURCE) -L$(CVC4_HOME)/build/src -L$(CVC4_HOME)/build/src/parser -lcvc4 -lcvc4parser

clean:
	rm -rf *.out
