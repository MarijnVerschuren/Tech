//
// Created by marijn on 2/12/23.
//
#include <stdio.h>
#include <malloc.h>

#include "../inc/sort.h"


void sort_test(void) {
	int64_t array[10] = {0, 0,/*4, -8,*/ 23, 1, 9, 20, -12, -8, 12, -20};
	sort(array, 10);
	for (uint8_t i = 0; i < 10; i++) {
		printf("%lld\n", array[i]);
	}
}


int main(int argc, char** argv) {
	sort_test();

	return 0;
}
