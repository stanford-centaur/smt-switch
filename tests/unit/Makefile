CXX=clang++
CXXFLAGS=""

main: sorts

sorts: unit-sort.cpp
	$(CXX) $(CXXFLAGS) -std=c++17 -I../../include/ unit-sort.cpp -o unit-sort.out

exceptions: unit-exceptions.cpp
	$(CXX) $(CXXFLAGS) -std=c++17 -I../../include/ unit-exceptions.cpp -o unit-exceptions.out

funcs: unit-func.cpp
	$(CXX) $(CXXFLAGS) -std=c++17 -I../../include/ unit-func.cpp -o unit-func.out

clean:
	rm -rf *.o *.out
