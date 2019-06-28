GENERIC_SRC=./src
GENERIC_INC=./include

BTOR=./btor
BTOR_HOME=./tests/btor/boolector

# SOURCE=$(GENERIC_SRC)/sort.cpp $(GENERIC_SRC)/ops.cpp $(GENERIC_SRC)/term.cpp $(BTOR_SRC)/boolector_factory.cpp $(BTOR_SRC)/boolector_solver.cpp $(BTOR_SRC)/boolector_extensions.cpp $(BTOR_SRC)/boolector_sort.cpp $(BTOR_SRC)/boolector_term.cpp $(BTOR_SRC)/boolector_fun.cpp

all: generic btor

generic: ops.o sort.o term.o

btor: boolector_extensions.o boolector_factory.o boolector_fun.o boolector_solver.o boolector_sort.o boolector_term.o

ops.o: $(GENERIC_SRC)/ops.cpp $(GENERIC_INC)/ops.h
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) $(GENERIC_SRC)/ops.cpp

sort.o: $(GENERIC_SRC)/sort.cpp $(GENERIC_INC)/sort.h
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) $(GENERIC_SRC)/sort.cpp

term.o: $(GENERIC_SRC)/term.cpp $(GENERIC_INC)/term.h
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) $(GENERIC_SRC)/term.cpp

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

libsmt-switch.so: ops.o sort.o term.o boolector_extensions.o boolector_factory.o boolector_fun.o boolector_solver.o boolector_sort.o boolector_term.o
	$(CXX) -shared -std=c++17 -Wl,-soname,libsmt-switch.so.1 -o libsmt-switch.so.1.0.0 -L$(BTOR_HOME)/build/lib ops.o sort.o term.o boolector_extensions.o boolector_factory.o boolector_fun.o boolector_solver.o boolector_sort.o boolector_term.o -lboolector -lm -pthread

btor-tests.out:
	$(CXX) -std=c++17 $(CXXFLAGS) $(DEBUG) -I$(GENERIC_INC) -o btor-tests.out btor-tests.cpp -L./ -lsmt-switch

install: libsmt-switch.so
	mkdir -p /usr/local/include/smt-switch
	cp -r ./include/* /usr/local/include/smt-switch/
	cp ./libsmt-switch.so.1.0.0 /usr/local/lib/
	ldconfig -n /usr/local/lib
	ln -s /usr/local/lib/libsmt-switch.so.1.0.0 /usr/local/lib/libsmt-switch.so

uninstall:
	rm -rf /usr/local/include/smt-switch
	rm -f /usr/local/lib/libsmt-switch.so.1.0.0
	rm -f /usr/local/lib/libsmt-switch.so.1
	rm -f /usr/local/lib/libsmt-switch.so

clean:
	rm -rf *.o
	rm -rf *.so.*
	rm -rf *.out
