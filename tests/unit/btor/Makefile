CXXFLAGS=""
BTOR_HOME="/home/makaim/repos/boolector"

btor-tests: btor-tests.cpp
	$(CXX) $(CXXFLAGS) -std=c++17 -I../../../include/ -I../../../include/btor/ -o btor-tests.out btor-tests.cpp $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -lpthread

clean:
	rm -rf *.o *.out
