GENERIC_SRC=./src
GENERIC_INC=./include

prefix=/usr/local

ifneq ($(wildcard Makefile.conf),)
include Makefile.conf
endif

export prefix
export BTOR_HOME
export CVC4_HOME

all: ops.o sort.o term.o

ops.o: $(GENERIC_SRC)/ops.cpp $(GENERIC_INC)/ops.h
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) $(GENERIC_SRC)/ops.cpp

sort.o: $(GENERIC_SRC)/sort.cpp $(GENERIC_INC)/sort.h
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) $(GENERIC_SRC)/sort.cpp

term.o: $(GENERIC_SRC)/term.cpp $(GENERIC_INC)/term.h
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) $(GENERIC_SRC)/term.cpp

libsmt-switch.so: ops.o sort.o term.o
	$(CXX) -shared -std=c++17 -Wl,-soname,libsmt-switch.so.1 -o libsmt-switch.so.1.0.0 ops.o sort.o term.o

install: libsmt-switch.so
	mkdir -p $(prefix)/include/smt-switch
	mkdir -p $(prefix)/lib
	cp -r ./include/* $(prefix)/include/smt-switch/
	cp ./libsmt-switch.so.1.0.0 $(prefix)/lib/
	ln -f -s libsmt-switch.so.1.0.0 $(prefix)/lib/libsmt-switch.so
	ln -f -s libsmt-switch.so.1.0.0 $(prefix)/lib/libsmt-switch.so.1
	@echo "Successfully installed: You might need to run ldconfig"

install-all: install install-btor install-cvc4

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
	./configure.sh --clean

clean-all: clean clean-solvers clean-tests

clean-solvers:
	$(MAKE) -C btor clean
	$(MAKE) -C cvc4 clean

clean-tests:
	$(MAKE) -C tests/btor clean
	$(MAKE) -C tests/cvc4 clean

SOLVERS = btor cvc4

.PHONY: $(SOLVERS)

$(SOLVERS):
	$(MAKE) -C $@

install-btor:
	echo $(BTOR_HOME)
	$(MAKE) -C btor install

install-cvc4:
	$(MAKE) -C cvc4 install

tests-btor: export LDFLAGS=-Wl,-rpath,$(prefix)/lib
tests-btor: export INCLUDE_PATH=-I$(prefix)/include
tests-btor: export LIB_PATH=-L$(prefix)/lib

tests-btor:
	$(MAKE) -C tests/btor all

tests-cvc4: export LDFLAGS=-Wl,-rpath,$(prefix)/lib
tests-cvc4: export INCLUDE_PATH=-I$(prefix)/include
tests-cvc4: export LIB_PATH=-L$(prefix)/lib

tests-cvc4:
	$(MAKE) -C tests/cvc4 all

tests: tests-btor tests-cvc4
