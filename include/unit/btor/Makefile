CXXFLAGS=""

unit-tests: unit-tests.cpp
	$(CXX) $(CXXFLAGS) -std=c++17 -I/home/makai/repos/generic-smt-api/include/ -I/home/makai/repos/generic-smt-api/include/btor/ -o unit-tests.out unit-tests.cpp /home/makai/repos/boolector/deps/btor2tools/build/btor2parser.o /usr/local/lib/libboolector.a /home/makai/repos/boolector/deps/lingeling/liblgl.a -lm -lpthread

clean:
	rm -rf *.o *.out
