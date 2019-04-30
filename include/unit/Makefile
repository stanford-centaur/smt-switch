CXX=clang++

main: sorts

sorts: unit-sort.cpp
	$(CXX) -std=c++17 -I../ unit-sort.cpp -o unit-sort.out

test: test.cpp
	$(CXX) -std=c++17 -I../ test.cpp -o test.out

clean:
	rm -rf *.o *.out
