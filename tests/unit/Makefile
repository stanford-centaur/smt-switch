CXX=clang++
CXXFLAGS=""
SOURCE=../../src/sort.cpp ../../src/ops.cpp ../../src/term.cpp

all: unit-sort.out unit-exception.out unit-fun.out unit-util.out
debug: all
debug: DEBUG=-g -D_DEBUG

main: sorts

unit-sort.out: unit-sort.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-sort.cpp $(SOURCE) -o unit-sort.out

unit-exception.out: unit-exceptions.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-exceptions.cpp $(SOURCE) -o unit-exception.out

unit-fun.out: unit-fun.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-fun.cpp $(SOURCE) -o unit-fun.out

unit-util.out: unit-util.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG) -std=c++17 -I../../include/ unit-util.cpp $(SOURCE) -o unit-util.out

clean:
	rm -rf *.o *.out
