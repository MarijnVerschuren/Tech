//
// Created by marijn on 2/12/23.
//
#include <stdio.h>
#include <malloc.h>
#include <string.h>
#include <time.h>

#include "../inc/seach.h"
#include "../inc/sort.h"

#define PADDING 32


void timed() {
	clock_t start, end;

	start = clock();			// start timer
	for (uint64_t i = 0; i < 10000000; i++) {
		compare_words("1234567890", "1234567890");
	}
	end = clock();				// stop timer
	printf("time:\t\t%f\n", ((double)(end - start)) / CLOCKS_PER_SEC);

	str padded_word = calloc(sizeof(char), PADDING);
	memcpy(padded_word, "1234567890", 4);

	start = clock();			// start timer
	for (uint64_t i = 0; i < 10000000; i++) {
		cmp_words(padded_word, padded_word);
	}
	end = clock();				// stop timer
	printf("time:\t\t%f\n", ((double)(end - start)) / CLOCKS_PER_SEC);
}


void search_test() {
	// normal text case
	str* words;
	uint64_t size = text_to_words("I'm trying to check if a a a value is zero in x86_64 assembly code zero zero zero", &words, PADDING);
	str padded_word = calloc(sizeof(char), PADDING);
	memcpy(padded_word, "zero", 4);
	sort(words, size, (comp_fn)cmp_words);

	printf("%lld\n", linear_count((const str*)words, size, padded_word, (comp_fn)cmp_words));
	printf("%lld\n", binary_count((const str*)words, size, padded_word, (comp_fn)cmp_words));

	for (uint64_t i = 0; i < size; i++) {
		free(words[i]);
	}	free(words);
	// \ normal text case

	// empty case
	size = 0;
	words = nullptr;
	printf("%lld\n", linear_count((const str*)words, size, padded_word, (comp_fn)cmp_words));
	printf("%lld\n", binary_count((const str*)words, size, padded_word, (comp_fn)cmp_words));
}


int main(int argc, char** argv) {
	search_test();
	timed();
	return 0;
}
