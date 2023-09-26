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


default: sort
	$(LINK) --shared -o $(BIN)stdlib.so $(STATIC)sort.o
	$(LINK) --relocatable -o $(BIN)stdlib.o $(STATIC)sort.o

sort:
	$(ASM) $(ASM_FLAGS) -o $(INT)sort.o $(SRC)sort.asm
	$(LINK) --relocatable -o $(STATIC)sort.o $(INT)sort.o