all : test

test : test.c memstream.o memstream.h
	cc -Wall -g -o $@ $< memstream.o

memstream.o : memstream.c memstream.h
	cc -Wall -g -c memstream.c

clean : .FORCE
	rm -rf *~ *.o test *.dSYM

.FORCE :
