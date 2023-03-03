CPPFLAGS=-I inc/
# Uncomment this to enable debug output and symbols
#CPPFLAGS+=-DDEBUG -O0 -g

CFLAGS=-Wall -std=c99
CXXFLAGS=-Wall -std=c++23

default: int/nethelper.o staticlib main

main: src/main.cpp bin/libcantcoap.a
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -fsanitize=address $< -o $@ int/cantcoap.o

int/cantcoap.o: src/cantcoap.cpp inc/cantcoap.h
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $< -c -o $@

int/nethelper.o: src/nethelper.c inc/nethelper.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -c -o $@

staticlib: bin/libcantcoap.a

bin/libcantcoap.a: int/cantcoap.o
	$(AR) $(ARFLAGS) bin/libcantcoap.a $^

clean:
	$(RM) int/* main bin/*