CXX=clang++
CXXFLAGS=""

main: sorts

sorts: unit-sort.cpp
	$(CXX) $(CXXFLAGS) -std=c++17 -I../ unit-sort.cpp -o unit-sort.out

exceptions: unit-exceptions.cpp
	$(CXX) $(CXXFLAGS) -std=c++17 -I../ unit-exceptions.cpp -o unit-exceptions.out

ops: unit-ops.cpp
	$(CXX) $(CXXFLAGS) -std=c++17 -I../ unit-ops.cpp -o unit-ops.out

test: test.cpp
	$(CXX) $(CXXFLAGS) -std=c++17 -I../ test.cpp -o test.out

clean:
	rm -rf *.o *.out
