SRC = ass3.c
TARGET = ass3

all : $(SRC)
	$(CC) -g $(SRC) -o $(TARGET)

test : clean $(SRC)
	$(CC) -g $(SRC) -o $(TARGET)
	@./test

clean : 
	@rm -f $(TARGET) out*
	@rm -rf kwinject.out .kwlp .kwps

klocwork:
	@kwcheck run

klocwork_after_makefile_change: clean
	@/opt/klocwork/kwenv.sh
	@kwcheck run
