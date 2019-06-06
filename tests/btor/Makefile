BTOR_HOME="/home/makaim/repos/boolector"
GENERIC_SRC=../../src
BTOR_SRC=../../btor/src
SOURCE=$(GENERIC_SRC)/sort.cpp $(GENERIC_SRC)/ops.cpp $(GENERIC_SRC)/term.cpp $(BTOR_SRC)/boolector_create.cpp $(BTOR_SRC)/boolector_solver.cpp $(BTOR_SRC)/boolector_extensions.cpp $(BTOR_SRC)/boolector_sort.cpp $(BTOR_SRC)/boolector_term.cpp $(BTOR_SRC)/boolector_fun.cpp

all: btor-tests.out btor-arrays.out btor-data-structures.out btor-indexed-op-tests.out
debug: all
debug: DEBUG=-g -D_DEBUG

btor-tests.out: btor-tests.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ -I../../btor/include/ -o btor-tests.out btor-tests.cpp $(SOURCE) $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

btor-arrays.out: btor-arrays.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ -I../../btor/include/ -o btor-arrays.out btor-arrays.cpp $(SOURCE) $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

btor-data-structures.out: btor-data-structures.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ -I../../btor/include/ -o btor-data-structures.out btor-data-structures.cpp $(SOURCE) $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

btor-indexed-op-tests.out: btor-indexed-op-tests.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ -I../../btor/include/ -o btor-indexed-op-tests.out btor-indexed-op-tests.cpp $(SOURCE) $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

clean:
	rm -rf *.o *.out
