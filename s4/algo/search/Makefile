C = gcc
ASM = nasm
CPP = g++
LINK = ld

C_FLAGS = -Wall -std=c99
CPP_FLAGS = -Wall -std=c++23
ASM_FLAGS = -Wall -f elf64

BIN = bin/
STATIC = bin/static/
INT = int/
SRC = src/


default: sort search
	$(LINK) --relocatable -o $(BIN)stdlib.o $(STATIC)sort.o $(STATIC)search.o

sort:
	$(ASM) $(ASM_FLAGS) -o $(INT)sort.o $(SRC)sort.asm
	$(LINK) --relocatable -o $(STATIC)sort.o $(INT)sort.o

search:
	$(ASM) $(ASM_FLAGS) -o $(INT)search.o $(SRC)search.asm
	$(LINK) --relocatable -o $(STATIC)search.o $(INT)search.o