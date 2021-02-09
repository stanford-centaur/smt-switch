all: smtlibparser.yy smtlibscanner.ll
	bison -o smtlibparser.cpp --defines=smtlibparser.h smtlibparser.yy
	flex -o smtlibscanner.cpp smtlibscanner.ll

clean:
	rm -f smtlibparser.h smtlibparser.cpp smtlibscanner.h smtlibscanner.cpp

# TODO get rid of old files -- smtlib.y smtlib.l smtlib_lexer.h
# Previous attempt mixing c/c++ -- didn't work out
# all: smtlib.l smtlib.y
# 	bison -d -v --defines=smtlib.h --output=smtlib.cpp smtlib.y
# 	flex smtlib.l
# 	g++ smtlib.cpp lex.smtlib.cc -lfl -o smtlibparser

# clean:
# 	rm -f smtlib.tab.* lex.smtlib.* smtlibparser
