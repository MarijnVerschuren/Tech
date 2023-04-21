SRC = ass2.c
TARGET = ass2

all : $(SRC)
	$(CC) -DTEST_TIME $(SRC) -o $(TARGET)

test : clean $(SRC)
	$(CC) $(SRC) -o $(TARGET)
	@./test

perf_tests : all
	@./perf

clean : 
	@rm -f $(TARGET) out.txt
	@rm -rf kwinject.out .kwlp .kwps

klocwork:
	@kwcheck run

klocwork_after_makefile_change: clean
	@/opt/klocwork/kwenv.sh
	@kwcheck run
