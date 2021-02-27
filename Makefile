all: smt-switch-parser-cvc4.cpp
	$(CXX) -static -std=c++11 -I./local/include/ -L./local/lib/ smt-switch-parser-cvc4.cpp -o smt-switch-parser-cvc4 -lfl -lsmt-switch-cvc4 -lsmt-switch -lgmp

clean:
	rm -f smtlibparser.h smtlibparser.cpp smtlibscanner.h smtlibscanner.cpp location.hh smt-switch-parser-cvc4

# TODO get rid of old files -- smtlib.y smtlib.l smtlib_lexer.h
# Previous attempt mixing c/c++ -- didn't work out
# all: smtlib.l smtlib.y
# 	bison -d -v --defines=smtlib.h --output=smtlib.cpp smtlib.y
# 	flex smtlib.l
# 	g++ smtlib.cpp lex.smtlib.cc -lfl -o smtlibparser

# clean:
# 	rm -f smtlib.tab.* lex.smtlib.* smtlibparser
