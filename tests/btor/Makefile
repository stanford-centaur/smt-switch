CXXFLAGS=-no-pie

all: btor-tests.out btor-arrays.out btor-data-structures.out btor-indexed-op-tests.out
debug: all
debug: DEBUG=-g -D_DEBUG

clean:
	rm -rf *.o *.out

# After installation
btor-tests.out: btor-tests.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o btor-tests.out btor-tests.cpp -lsmt-switch -lsmt-switch-btor

btor-arrays.out: btor-arrays.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o btor-arrays.out btor-arrays.cpp -lsmt-switch -lsmt-switch-btor

btor-data-structures.out: btor-data-structures.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o btor-data-structures.out btor-data-structures.cpp -lsmt-switch -lsmt-switch-btor

btor-indexed-op-tests.out: btor-indexed-op-tests.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o btor-indexed-op-tests.out btor-indexed-op-tests.cpp -lsmt-switch -lsmt-switch-btor
