CXX=clang++
CXXFLAGS=""

all: sorts exceptions funcs util
debug: all
debug: DEBUG=-g -D_DEBUG

main: sorts

sorts: unit-sort.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-sort.cpp -o unit-sort.out

exceptions: unit-exceptions.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-exceptions.cpp -o unit-exceptions.out

funcs: unit-func.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-func.cpp -o unit-func.out

util: unit-util.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-util.cpp -o unit-util.out

clean:
	rm -rf *.o *.out
