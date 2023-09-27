//
// Created by marijn on 2/12/23.
//
#include <stdio.h>
#include <malloc.h>
#include <time.h>

#include "../inc/sort.h"
#include "../inc/test_array.h"



void sort_test(uint8_t print) {
	clock_t start, end;
	if(print) {
		printf("before:\t["); for (uint64_t i = 0; i < SIZE; i++) {
			printf("%lld", array[i]);
			if (i < SIZE - 1) { printf(", "); }
		} printf("]\n");
	}

	start = clock();			// start timer
	bubble_sort(array, SIZE);
	end = clock();				// stop timer
	printf("time:\t%f\n", ((double)(end - start)) / CLOCKS_PER_SEC);

	if(print) {
		printf("before:\t["); for (uint64_t i = 0; i < SIZE; i++) {
			printf("%lld", array[i]);
			if (i < SIZE - 1) { printf(", "); }
		} printf("]\n");
	}
}


int main(int argc, char** argv) {
	sort_test(0);

	return 0;
}
