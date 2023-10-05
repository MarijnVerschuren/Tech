//
// Created by marijn on 2/12/23.
//
#include <stdio.h>
#include <malloc.h>
#include <string.h>
#include <time.h>

#include "../inc/seach.h"
#include "../inc/sort.h"


void search_test() {
	clock_t start, end;

	start = clock();			// start timer
	for (uint64_t i = 0; i < 10000000; i++) {
		(void)linear_count("ththethethethethethe", "the");
	}
	end = clock();				// stop timer
	printf("time:\t\t%f\n", ((double)(end - start)) / CLOCKS_PER_SEC);

	printf("%lld\n", linear_count("ththethethethethethe", "the"));
}


void sort_test() {
	str* words;
	uint64_t size = text_to_words("I'm trying to check if a a a value is zero in x86_64 assembly code zero zero zero", &words);
	(void)words;
	bubble_sort(words, size, (comp_fn)compare_words);
	for (uint64_t i = 0; i < size; i++) { printf("%s\n", words[i]); } printf("\n\n");
	printf("%lld\n", linear_count_a(words, size, "zero"));

}


int main(int argc, char** argv) {
	sort_test();
	//search_test();

	return 0;
}
