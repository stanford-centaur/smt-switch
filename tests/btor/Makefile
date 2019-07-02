BTOR_HOME="./boolector"
GENERIC_SRC=../../src
BTOR_SRC=../../btor/src
SOURCE=$(GENERIC_SRC)/sort.cpp $(GENERIC_SRC)/ops.cpp $(GENERIC_SRC)/term.cpp $(BTOR_SRC)/boolector_factory.cpp $(BTOR_SRC)/boolector_solver.cpp $(BTOR_SRC)/boolector_extensions.cpp $(BTOR_SRC)/boolector_sort.cpp $(BTOR_SRC)/boolector_term.cpp $(BTOR_SRC)/boolector_fun.cpp
CXXFLAGS=-no-pie

all: btor-tests.out btor-arrays.out btor-data-structures.out btor-indexed-op-tests.out
debug: all
debug: DEBUG=-g -D_DEBUG

clean:
	rm -rf *.o *.out

# After installation
btor-tests.out: btor-tests.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o btor-tests.out btor-tests.cpp -lsmt-switch -lsmt-switch-btor

btor-arrays.out: btor-arrays.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o btor-arrays.out btor-arrays.cpp -lsmt-switch -lsmt-switch-btor

btor-data-structures.out: btor-data-structures.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o btor-data-structures.out btor-data-structures.cpp -lsmt-switch -lsmt-switch-btor

btor-indexed-op-tests.out: btor-indexed-op-tests.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o btor-indexed-op-tests.out btor-indexed-op-tests.cpp -lsmt-switch -lsmt-switch-btor
