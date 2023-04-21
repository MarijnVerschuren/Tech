
all : ass1.c
	$(CC) -g -DTEST_TIME ass1.c -o ass1

test : clean ass1.c
	$(CC) ass1.c -o ass1
	@./test

perf_tests : all
	@./perf

clean : 
	@rm -f ass1 out.txt
	@rm -rf kwinject.out .kwlp .kwps


klocwork:
	@kwcheck run

klocwork_after_makefile_change: clean
	@/opt/klocwork/kwenv.sh
	@kwcheck run
