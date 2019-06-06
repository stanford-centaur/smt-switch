BTOR_HOME="/home/makaim/repos/boolector"
SOURCE=../../src/sort.cpp ../../src/ops.cpp ../../src/term.cpp ../../src/btor/boolector_create.cpp ../../src/btor/boolector_solver.cpp ../../src/btor/boolector_extensions.cpp ../../src/btor/boolector_sort.cpp ../../src/btor/boolector_term.cpp ../../src/btor/boolector_fun.cpp

all: btor-tests.out btor-arrays.out btor-data-structures.out btor-indexed-op-tests.out
debug: all
debug: DEBUG=-g -D_DEBUG

btor-tests.out: btor-tests.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ -I../../include/btor/ -o btor-tests.out btor-tests.cpp $(SOURCE) $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

btor-arrays.out: btor-arrays.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ -I../../include/btor/ -o btor-arrays.out btor-arrays.cpp $(SOURCE) $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

btor-data-structures.out: btor-data-structures.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ -I../../include/btor/ -o btor-data-structures.out btor-data-structures.cpp $(SOURCE) $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

btor-indexed-op-tests.out: btor-indexed-op-tests.cpp $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ -I../../include/btor/ -o btor-indexed-op-tests.out btor-indexed-op-tests.cpp $(SOURCE) $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

clean:
	rm -rf *.o *.out
