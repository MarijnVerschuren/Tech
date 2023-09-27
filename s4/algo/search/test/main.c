//
// Created by marijn on 2/12/23.
//
#include <stdio.h>
#include <malloc.h>
#include <string.h>
#include <time.h>

#include "../inc/seach.h"



void search_test() {
	clock_t start, end;

	start = clock();			// start timer
	for (uint64_t i = 0; i < 10000000; i++) {
		(void)linear_search("ththethethethethethe", "the");
	}
	end = clock();				// stop timer
	printf("time:\t\t%f\n", ((double)(end - start)) / CLOCKS_PER_SEC);

	printf("%lld\n", linear_search("ththethethethethethe", "the"));
}


int main(int argc, char** argv) {
	search_test();

	return 0;
}
