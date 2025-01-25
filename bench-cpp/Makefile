CXX=clang++
RM=rm -f
CPPFLAGS=-O3

all: bench

bench: bench.o
	$(CXX) -o bench bench.o

bench.o: bench.cpp

clean:
	$(RM) bench.o
	$(RM) bench
