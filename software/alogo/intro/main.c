#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))



uint32_t arr_max(uint32_t* arr, uint32_t len) {
	uint32_t max_n = 0;
	for (uint32_t i = 0; i < len; i++) {
		max_n = MAX(arr[i], max_n);
	}
	return max_n;
}

uint32_t find_smallest_n_occuring_k_times(uint32_t* arr, uint32_t len, uint32_t k) {	// O(n)
	if (len > 100000 || k > 100000) { return -1; }					// len and k cant be higher than 100000
	uint32_t m = arr_max(arr, len);									// finding the max value: O(n)
	if (m > 100000) { return -1; }									// no value in "arr" can be higher than 100000
	m++;															// m is incremented by one so that the count lookup table can hold the 100000 values
	

	uint32_t* n_count = calloc(m, 4);								// initialized array to count occurances for each number in "arr"
	for (uint32_t i = 0; i < len; i++) { n_count[arr[i]]++; }		// counting occurances of the numbers in "arr": O(n)
	uint32_t res = -1;												// result initialized with invalid value
	for (uint32_t i = 0; i < m; i++) {
		if (n_count[i] == k) { res = i; break; }					//  searching for the smallest number that occurs k times: O(n)
	}

	free(n_count);
	return res;
}

uint64_t find_max_difference_between_sums_of_k_elements(uint32_t* arr, uint32_t len, uint32_t k) {	// O(n)
	if (len > 999 || !k || k >= len) { return 0; }									// len has to be smaller than 1000 and k cant be zero and has to be smaller than len
	uint32_t m = arr_max(arr, len);													// finding the max value: O(n)
	if (m > 100000) { return 0; }													// no value in "arr" can be higher than 100000
	m++;																			// m is incremented by one so that the count lookup table can hold the 100000 values

	uint32_t* n_count = calloc(m, 4);												// initialized array to count occurances for each number in "arr"
	for (uint32_t i = 0; i < len; i++) { n_count[arr[i]]++; }						// counting occurances of the numbers in "arr": O(n)
	uint64_t min_sum = 0, max_sum = 0;
	uint32_t min_sum_size = 0, max_sum_size = 0;
	uint32_t current_count;
	for (uint32_t i = 0; i < m && (min_sum_size != k || max_sum_size != k); i++) {	// find the min and max sums: O(n)
		current_count = MIN(n_count[i], k - min_sum_size);							// calculate how many times the number i can be added to the min sum
		if (current_count) {
			min_sum += i * current_count;
			min_sum_size += current_count;
		}
		current_count - MIN(n_count[m-i], k - max_sum_size);						// calculate how many times the number i can be added to the max sum
		if (current_count) {
			max_sum += ((m-i)+1) * current_count;									// +1 because we are indexing from the end of the count lookup table
			max_sum_size += current_count;
		}
	}
	
	free(n_count);
	return max_sum - min_sum;
}


void uint_sort(uint32_t* arr, uint32_t len) {	// O(n)
	uint32_t m = arr_max(arr, len) + 1;								// calculate length of lookup table
	if (m > (1 << 20)) { return; }									// make sure that no more than 4Mib is allocated
	uint32_t* n_count = calloc(m, 4);
	for (uint32_t i = 0; i < len; i++) { n_count[arr[i]]++; }		// counting occurances of the numbers in "arr": O(n)
	for (uint32_t i = 0; i < m; i++) {
		for (uint32_t j = 0; j < n_count[i]; j++) { *arr++ = i; }	// reconstruction the array from lookup table O(n)
	}
}

/* Split uint sort:
 *  let our data type be an uint32_t
 *  we will devide this data into 4 'digits' of base256 so 8 bits
 *	then we will apply uint_sort four times from least to most significant digit
 *	because we do not want to calculate the max value at each step we are going to be allocating a (256 * uint64_t => 2Kib) workspace to store the count lookup table (this is reused each digit)
 *	to isolate digit:									"(val >> (digit_n * 8)) & 0xff"
 *	trick to keep track of index in the result array:	"count[n + 1] += count[n]"			(this calculates the accumalative size (check if this is usable))
 * */

int main(uint32_t argc, const char** argv) {
	uint32_t len = 0;
	scanf("%u", &len);
	
	if (!len) { return -1; }										// you cant have an array of size 0
	uint32_t* arr = malloc(len * 4);								// uninitialzed array for numbers (these will be set)
	for (uint32_t i = 0; i < len; i++) { scanf("%u ", &arr[i]); }	// set array indecies with data from stdin
	
	uint32_t k = 0;
	scanf("%u", &k);
	
	/*
	uint32_t res = find_smallest_n_occuring_k_times(arr, len, k);
	if (res == 0xffffffff)	{ printf("error or not found\n"); }
	else					{ printf("%u is the smallest number that occurs %u times\n", res, k); }
	*/
	/*
	uint64_t res = find_max_difference_between_sums_of_k_elements(arr, len, k);
	if (!res)				{ printf("error or difference is 0\n"); }
	else					{ printf("the maximum difference between sums made from %u elements of \"arr\" is: %u\n", k, res); }
	*/

	uint_sort(arr, len);
	for (uint32_t i = 0; i < len; i++) {
		printf("%u ", arr[i]);
	}; printf("\n");
	
	free(arr);
	return 0;
}
