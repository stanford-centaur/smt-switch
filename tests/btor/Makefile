BTOR_HOME="/home/makaim/repos/boolector"

all: btor-tests btor-arrays btor-data-structures
debug: all
debug: DEBUG=-g -D_DEBUG

btor-tests: btor-tests.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ -I../../include/btor/ -o btor-tests.out btor-tests.cpp $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

btor-arrays: btor-arrays.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ -I../../include/btor/ -o btor-arrays.out btor-arrays.cpp $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

btor-data-structures: btor-data-structures.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ -I../../include/btor/ -o btor-data-structures.out btor-data-structures.cpp $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

clean:
	rm -rf *.o *.out
