PRODUCT=ass6_2

CXXFLAGS=-Wall -Werror -Wextra -pedantic -ggdb -O0 $(CPPFLAGS)

SOURCES=$(wildcard *.cpp) 

HEADERS=$(wildcard *.h) 

CXX=g++

.PHONY: all 

all: $(PRODUCT)

$(PRODUCT): $(SOURCES) $(HEADERS)
	@$(CXX) $(CXXFLAGS) $(SOURCES) -o $@

clean:
	@rm -rf $(PRODUCT) out.txt
	@rm -rf kwinject.out .kwlp .kwps

klocwork:
	@kwcheck run

klocwork_after_makefile_change: clean
	@/opt/klocwork/kwenv.sh
	@kwcheck run

test: $(PRODUCT)
	./test
