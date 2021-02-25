#
CC=gcc
CFLAGS=-Wall -lbsd
GMP=-lgmp

all: test.o rsa_pss.o sha2.o
	$(CC) $(CFLAGS) -o test test.o rsa_pss.o sha2.o $(GMP)

test.o: test.c rsa_pss.h
	$(CC) $(CFLAGS) -c test.c

rsa_pss.o: rsa_pss.c rsa_pss.h
	$(CC) $(CFLAGS) -c rsa_pss.c

sha2.o: sha2.c sha2.h
	$(CC) $(CFLAGS) -c sha2.c

clean:
	rm -rf *.o
	rm -rf test
