GENERIC_SRC=./src
GENERIC_INC=./include

BTOR=./btor
BTOR_HOME=./tests/btor/boolector

prefix=/usr/local

# SOURCE=$(GENERIC_SRC)/sort.cpp $(GENERIC_SRC)/ops.cpp $(GENERIC_SRC)/term.cpp $(BTOR_SRC)/boolector_factory.cpp $(BTOR_SRC)/boolector_solver.cpp $(BTOR_SRC)/boolector_extensions.cpp $(BTOR_SRC)/boolector_sort.cpp $(BTOR_SRC)/boolector_term.cpp $(BTOR_SRC)/boolector_fun.cpp

all: ops.o sort.o term.o

ops.o: $(GENERIC_SRC)/ops.cpp $(GENERIC_INC)/ops.h
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) $(GENERIC_SRC)/ops.cpp

sort.o: $(GENERIC_SRC)/sort.cpp $(GENERIC_INC)/sort.h
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) $(GENERIC_SRC)/sort.cpp

term.o: $(GENERIC_SRC)/term.cpp $(GENERIC_INC)/term.h
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) $(GENERIC_SRC)/term.cpp

libsmt-switch.so: ops.o sort.o term.o
	$(CXX) -shared -std=c++17 -Wl,-soname,libsmt-switch.so.1 -o libsmt-switch.so.1.0.0 -L$(BTOR_HOME)/build/lib ops.o sort.o term.o

install: libsmt-switch.so
	mkdir -p $(prefix)/include/smt-switch
	mkdir -p $(prefix)/lib
	cp -r ./include/* $(prefix)/include/smt-switch/
	cp ./libsmt-switch.so.1.0.0 $(prefix)/lib/
	ldconfig -n $(prefix)/lib
	ln -f -s $(prefix)/lib/libsmt-switch.so.1.0.0 $(prefix)/lib/libsmt-switch.so

install-all: install btor-install cvc4-install
	ldconfig -n $(prefix)/lib

uninstall:
	rm -rf $(prefix)/include/smt-switch
	rm -f $(prefix)/lib/libsmt-switch.so.1.0.0
	rm -f $(prefix)/lib/libsmt-switch.so.1
	rm -f $(prefix)/lib/libsmt-switch.so

uninstall-all: uninstall
	$(MAKE) -C btor uninstall
	$(MAKE) -C cvc4 uninstall

clean:
	rm -rf *.o
	rm -rf *.so.*
	rm -rf *.out

clean-all: clean
	$(MAKE) -C btor clean
	$(MAKE) -C cvc4 clean

SOLVERS = btor cvc4

.PHONY: $(SOLVERS)

$(SOLVERS):
	$(MAKE) -C $@

btor-install:
	$(MAKE) -C btor install

cvc4-install:
	$(MAKE) -C cvc4 install
