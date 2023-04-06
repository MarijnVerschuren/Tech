SRC = mergeSortMT.cpp
TARGET = mergeSort
CC = g++

all : $(SRC)
	$(CC) -g $(SRC) -o $(TARGET) -lpthread

test : clean $(SRC)
	$(CC) -g $(SRC) -o $(TARGET) -lpthread
	@./test

clean : 
	@rm -f $(TARGET) out*
	@rm -rf kwinject.out .kwlp .kwps

klocwork:
	@kwcheck run

klocwork_after_makefile_change: clean
	@/opt/klocwork/kwenv.sh
	@kwcheck run
