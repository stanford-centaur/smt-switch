GENERIC_SRC=../src
GENERIC_INC=../include

CVC4=./
CVC4_HOME=./CVC4

all: libsmt-switch-cvc4.so

cvc4:
	./build.sh

cvc4_factory.o: $(GENERIC_INC)/cvc4_factory.h $(CVC4)/src/cvc4_factory.cpp
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) -I$(GENERIC_SRC) -I$(CVC4)/include -I$(CVC4_HOME)/src/ -I$(CVC4_HOME)/src/api -I$(CVC4_HOME)/src/include $(CVC4)/src/cvc4_factory.cpp

cvc4_fun.o: $(CVC4)/include/cvc4_fun.h $(CVC4)/src/cvc4_fun.cpp
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) -I$(GENERIC_SRC) -I$(CVC4)/include -I$(CVC4_HOME)/src/ -I$(CVC4_HOME)/src/api -I$(CVC4_HOME)/src/include $(CVC4)/src/cvc4_fun.cpp

cvc4_solver.o: $(CVC4)/include/cvc4_solver.h $(CVC4)/src/cvc4_solver.cpp
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) -I$(GENERIC_SRC) -I$(CVC4)/include -I$(CVC4_HOME)/src/ -I$(CVC4_HOME)/src/api -I$(CVC4_HOME)/src/include $(CVC4)/src/cvc4_solver.cpp

cvc4_sort.o: $(CVC4)/include/cvc4_sort.h $(CVC4)/src/cvc4_sort.cpp
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) -I$(GENERIC_SRC) -I$(CVC4)/include -I$(CVC4_HOME)/src/ -I$(CVC4_HOME)/src/api -I$(CVC4_HOME)/src/include $(CVC4)/src/cvc4_sort.cpp

cvc4_term.o: $(CVC4)/include/cvc4_term.h $(CVC4)/src/cvc4_term.cpp
	$(CXX) -std=c++17 -fPIC -g -c -Wall -I$(GENERIC_INC) -I$(GENERIC_SRC) -I$(CVC4)/include -I$(CVC4_HOME)/src/ -I$(CVC4_HOME)/src/api -I$(CVC4_HOME)/src/include $(CVC4)/src/cvc4_term.cpp

libsmt-switch-cvc4.so: cvc4 cvc4_factory.o cvc4_fun.o cvc4_solver.o cvc4_sort.o cvc4_term.o $(CVC4_HOME)/build/src/parser/libcvc4parser.a $(CVC4_HOME)/build/src/libcvc4.a
	$(CXX) -shared -std=c++17 -Wl,-soname,libsmt-switch-cvc4.so.1 -o libsmt-switch-cvc4.so.1.0.0 cvc4_factory.o cvc4_fun.o cvc4_solver.o cvc4_sort.o cvc4_term.o $(CVC4_HOME)/build/src/parser/libcvc4parser.a $(CVC4_HOME)/build/src/libcvc4.a -lgmp

install: libsmt-switch-cvc4.so
	mkdir -p /usr/local/include/smt-switch
	cp -r ./include/* /usr/local/include/smt-switch/
	cp ./libsmt-switch-cvc4.so.1.0.0 /usr/local/lib/
	ldconfig -n /usr/local/lib
	ln -f -s /usr/local/lib/libsmt-switch-cvc4.so.1.0.0 /usr/local/lib/libsmt-switch-cvc4.so

uninstall:
	rm -rf /usr/local/include/smt-switch
	rm -f /usr/local/lib/libsmt-switch-cvc4.so.1.0.0
	rm -f /usr/local/lib/libsmt-switch-cvc4.so.1
	rm -f /usr/local/lib/libsmt-switch-cvc4.so

clean:
	rm -rf *.o *.so.*
	rm -rf CVC4
