CXXFLAGS=-no-pie

all: cvc4-tests.out cvc4-arrays.out cvc4-data-structures.out cvc4-indexed-op-tests.out cvc4_test.out

debug: all
debug: DEBUG=-g -D_DEBUG

# After install
cvc4-tests.out: cvc4-tests.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o cvc4-tests.out cvc4-tests.cpp -lsmt-switch -lsmt-switch-cvc4

cvc4-arrays.out: cvc4-arrays.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o cvc4-arrays.out cvc4-arrays.cpp -lsmt-switch -lsmt-switch-cvc4

cvc4-data-structures.out: cvc4-data-structures.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o cvc4-data-structures.out cvc4-data-structures.cpp -lsmt-switch -lsmt-switch-cvc4

cvc4-indexed-op-tests.out: cvc4-indexed-op-tests.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -o cvc4-indexed-op-tests.out cvc4-indexed-op-tests.cpp -lsmt-switch -lsmt-switch-cvc4

cvc4_test.out: cvc4_test.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I/usr/local/include/smt-switch -o cvc4_test.out cvc4_test.cpp -lsmt-switch -lsmt-switch-cvc4

clean:
	rm -rf *.out
