//
// Created by marijn on 2/12/23.
//
#include <stdio.h>
#include <malloc.h>
#include <string.h>
#include <time.h>

#include "../inc/seach.h"

#define PADDING 32


void compare_test() {
	str padded_word_a = calloc(sizeof(char), PADDING);
	str padded_word_b = calloc(sizeof(char), PADDING);
	memcpy(padded_word_a, "1234567890", 11);
	memcpy(padded_word_b, "1234567891", 11);

	printf("compare_words\t(null, null) == 0\t->\t%d\n", compare_words(nullptr, nullptr) == 0);
	printf("cmp_words\t\t(null, null) == 0\t->\t%d\n", cmp_words(nullptr, nullptr) == 0);

	printf("compare_words\t(eq, eq) == 0\t\t->\t%d\n", compare_words("1234567890", "1234567890") == 0);
	printf("cmp_words\t\t(eq, eq) == 0\t\t->\t%d\n", cmp_words(padded_word_a, padded_word_a) == 0);

	printf("compare_words\t(lt, gt) == -1\t\t->\t%d\n", compare_words("1234567890", "1234567891") == -1);
	printf("cmp_words\t\t(lt, gt) == -1\t\t->\t%d\n", cmp_words(padded_word_a, padded_word_b) == -1);

	printf("compare_words\t(gt, lt) == 1\t\t->\t%d\n", compare_words("1234567891", "1234567890") == 1);
	printf("cmp_words\t\t(gt, lt) == 1\t\t->\t%d\n", cmp_words(padded_word_b, padded_word_a) == 1);

	printf("\n");

	clock_t start, end;

	start = clock();			// start timer
	for (uint64_t i = 0; i < 10000000; i++) {
		compare_words("1234567890", "1234567891");
	}
	end = clock();				// stop timer
	printf("compare_words:\t\t%f\n", ((double)(end - start)) / CLOCKS_PER_SEC);

	start = clock();			// start timer
	for (uint64_t i = 0; i < 10000000; i++) {
		cmp_words(padded_word_a, padded_word_b);
	}
	end = clock();				// stop timer
	printf("cmp_words:\t\t\t%f\n", ((double)(end - start)) / CLOCKS_PER_SEC);

	printf("\n");
}


void search_test() {
	clock_t start, end;

	// normal text case
	str* words;
	uint64_t size = text_to_words("I'm trying to check if a a a value is zero in x86_64 assembly code zero zero zero", &words, PADDING);
	str padded_word = malloc(PADDING);
	memset(padded_word, 0x00, PADDING);
	memcpy(padded_word, "zero", 5);
	sort(words, size, (comp_fn)cmp_words);

	printf("linear_count (words, size, padded_word, cmp_words) == 4\t->\t%d\n", linear_count((const str*)words, size, padded_word, (comp_fn)cmp_words) == 4);
	printf("binary_count (words, size, padded_word, cmp_words) == 4\t->\t%d\n", binary_count((const str*)words, size, padded_word, (comp_fn)cmp_words) == 4);

	for (uint64_t i = 0; i < size; i++) {
		free(words[i]);
	}	free(words);

	// empty case
	printf("linear_count (null, 0, null, null) == 0\t->\t\t\t\t\t%d\n", linear_count(nullptr, 0, nullptr, (comp_fn)nullptr) == 0);
	printf("binary_count (null, 0, null, null) == 0\t->\t\t\t\t\t%d\n", binary_count(nullptr, 0, nullptr, (comp_fn)nullptr) == 0);

	printf("\n");

	// speed test
	char* filename = "/home/marijn/Github/Tech/s4/algo/search/test/hs_err_pid98322.log";
	FILE* file = fopen(filename, "r");
	if (file == NULL) { return; }
	fseek(file, 0, SEEK_END);
	uint64_t file_size = ftell(file);
	rewind(file);

	str buffer = malloc(file_size + 1);
	fread(buffer, sizeof(char), file_size, file);
	buffer[file_size] = '\0'; fclose(file);

	size = text_to_words(buffer, &words, PADDING);
	memset(padded_word, 0x00, PADDING);
	memcpy(padded_word, " ", 2);


	start = clock();			// start timer
	sort(words, size, (comp_fn)cmp_words);
	end = clock();				// stop timer
	printf("sort:\t\t\t\t%f\n", ((double)(end - start)) / CLOCKS_PER_SEC);

	start = clock();			// start timer
	for (uint64_t i = 0; i < 100; i++) {
		linear_count((const str*) words, size, padded_word, (comp_fn) cmp_words);
	}
	end = clock();				// stop timer
	printf("linear search:\t\t%f\n", ((double)(end - start)) / CLOCKS_PER_SEC);

	start = clock();			// start timer
	for (uint64_t i = 0; i < 100; i++) {
		binary_count((const str*)words, size, padded_word, (comp_fn)cmp_words);
	}
	end = clock();				// stop timer
	printf("binary search:\t\t%f\n", ((double)(end - start)) / CLOCKS_PER_SEC);

}


int main(int argc, char** argv) {
	compare_test();
	search_test();
	return 0;
}
