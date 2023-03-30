SRC =main.cpp
TARGET = mt_example
CC = g++

all : $(SRC)
	$(CC) -g $(SRC) -o $(TARGET) -lpthread

clean : 
	@rm -f $(TARGET) 
	@rm -rf kwinject.out .kwlp .kwps

klocwork:
	@kwcheck run

klocwork_after_makefile_change: clean
	@/opt/klocwork/kwenv.sh
	@kwcheck run
