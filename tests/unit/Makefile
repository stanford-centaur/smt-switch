CXX=clang++
CXXFLAGS=""
SOURCE="../../src/sort.cpp"

all: sorts exceptions funs util
debug: all
debug: DEBUG=-g -D_DEBUG

main: sorts

sorts: unit-sort.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-sort.cpp $(SOURCE) -o unit-sort.out

exceptions: unit-exceptions.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-exceptions.cpp $(SOURCE) -o unit-exceptions.out

funs: unit-fun.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-fun.cpp $(SOURCE) -o unit-fun.out

util: unit-util.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-util.cpp $(SOURCE) -o unit-util.out

clean:
	rm -rf *.o *.out
