GLOBAL_FLAGS = -I inc/ -Wall -O0
C_FLAGS = -std=c99
CPP_FLAGS = -std=c++23

default: int/nethelper.o staticlib main

main:
	$(CXX) $(GLOBAL_FLAGS) $(CXXFLAGS) -fsanitize=address src/main.cpp int/cantcoap.o int/nethelper.o -o $@

int/cantcoap.o: src/cantcoap.cpp inc/cantcoap.h
	$(CXX) $(GLOBAL_FLAGS) $(CXXFLAGS) $< -c -o $@

int/nethelper.o: src/nethelper.c inc/nethelper.h
	$(CC) $(GLOBAL_FLAGS) $(CFLAGS) -c $< -c -o $@

staticlib: bin/libcantcoap.a

bin/libcantcoap.a: int/cantcoap.o
	$(AR) $(ARFLAGS) bin/libcantcoap.a $^

clean:
	$(RM) int/* main bin/*