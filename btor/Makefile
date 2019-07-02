GENERIC_SRC=../src
GENERIC_INC=../include

BTOR=./
BTOR_HOME=./boolector

prefix=/usr/local

all: boolector libsmt-switch-btor.so

boolector:
	./build.sh

boolector_extensions.o: $(BTOR)/include/boolector_extensions.h $(BTOR)/src/boolector_extensions.cpp
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) -I$(GENERIC_SRC) -I$(BTOR)/include -I$(BTOR_HOME)/src/ $(BTOR)/src/boolector_extensions.cpp

boolector_factory.o: $(GENERIC_INC)/boolector_factory.h $(BTOR)/src/boolector_factory.cpp
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) -I$(GENERIC_SRC) -I$(BTOR)/include -I$(BTOR_HOME)/src/ $(BTOR)/src/boolector_factory.cpp

boolector_fun.o: $(BTOR)/include/boolector_fun.h $(BTOR)/src/boolector_fun.cpp
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) -I$(GENERIC_SRC) -I$(BTOR)/include -I$(BTOR_HOME)/src/ $(BTOR)/src/boolector_fun.cpp

boolector_solver.o: $(BTOR)/include/boolector_solver.h $(BTOR)/src/boolector_solver.cpp
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) -I$(GENERIC_SRC) -I$(BTOR)/include -I$(BTOR_HOME)/src/ $(BTOR)/src/boolector_solver.cpp

boolector_sort.o: $(BTOR)/include/boolector_sort.h $(BTOR)/src/boolector_sort.cpp
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) -I$(GENERIC_SRC) -I$(BTOR)/include -I$(BTOR_HOME)/src/ $(BTOR)/src/boolector_sort.cpp

boolector_term.o: $(BTOR)/include/boolector_term.h $(BTOR)/src/boolector_term.cpp
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) -I$(GENERIC_SRC) -I$(BTOR)/include -I$(BTOR_HOME)/src/ $(BTOR)/src/boolector_term.cpp

libsmt-switch-btor.so: boolector boolector_extensions.o boolector_factory.o boolector_fun.o boolector_solver.o boolector_sort.o boolector_term.o $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a
	$(CXX) -shared -std=c++17 -Wl,-soname,libsmt-switch-btor.so.1 -o libsmt-switch-btor.so.1.0.0 boolector_extensions.o boolector_factory.o boolector_fun.o boolector_solver.o boolector_sort.o boolector_term.o $(BTOR_HOME)/deps/btor2tools/build/btor2parser.o $(BTOR_HOME)/build/lib/libboolector.a $(BTOR_HOME)/deps/lingeling/liblgl.a -lm -pthread

install: libsmt-switch-btor.so
	mkdir -p $(prefix)/include/smt-switch
	mkdir -p $(prefix)/lib
	cp -r ./include/* $(prefix)/include/smt-switch/
	cp ./libsmt-switch-btor.so.1.0.0 $(prefix)/lib/
	ldconfig -n $(prefix)/lib
	ln -f -s $(prefix)/lib/libsmt-switch-btor.so.1.0.0 $(prefix)/lib/libsmt-switch-btor.so

uninstall:
	rm -rf $(prefix)/include/smt-switch
	rm -f $(prefix)/lib/libsmt-switch-btor.so.1.0.0
	rm -f $(prefix)/lib/libsmt-switch-btor.so.1
	rm -f $(prefix)/lib/libsmt-switch-btor.so

clean:
	rm -rf *.o *.so.*
	rm -rf boolector
