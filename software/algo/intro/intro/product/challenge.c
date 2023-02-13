#include "challenge.h"




#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))



uint32_t arr_max(uint32_t* arr, uint32_t len) {
	uint32_t max_n = 0;
	for (uint32_t i = 0; i < len; i++) {
		max_n = MAX(arr[i], max_n);
	}
	return max_n;
}



int FindSmallestNumberThatIsRepeatedKTimes(
            uint32_t* arr, uint32_t len, uint32_t k, uint32_t* smallestNumber)
{
    
    if (len > 100000 || k > 100000) { return -1; }					// len and k cant be higher than 100000
    uint32_t m = arr_max(arr, len);									// finding the max value: O(n)
    if (m > 100000) { return -1; }									// no value in "arr" can be higher than 100000
    m++;															// m is incremented by one so that the count lookup table can hold the 100000 values
	

    uint32_t* n_count = calloc(m, 4);								// initialized array to count occurances for each number in "arr"
    for (uint32_t i = 0; i < len; i++) { n_count[arr[i]]++; }		// counting occurances of the numbers in "arr": O(n)
    for (uint32_t i = 0; i < m; i++) {
		    if (n_count[i] == k) { *smallestNumber = i; break; }					//  searching for the smallest number that occurs k times: O(n)
    }

    free(n_count);
    return 0;
}

int ComputeDifferenceBetweenMaxAndMinSumOfKElements_0(
    uint32_t* arr, uint32_t len, uint32_t k, uint32_t* res) {
    
    if (len > 999 || !k || k >= len) { return -1; }									// len has to be smaller than 1000 and k cant be zero and has to be smaller than len
    uint32_t m = arr_max(arr, len);													// finding the max value: O(n)
	  if (m > 100000) { return -1; }													// no value in "arr" can be higher than 100000
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
		  current_count = MIN(n_count[m-i], k - max_sum_size);						// calculate how many times the number i can be added to the max sum
		  if (current_count) {
			  max_sum += ((m-i)+1) * current_count;									// +1 because we are indexing from the end of the count lookup table
			  max_sum_size += current_count;
		  }
	  }

	  *res = max_sum - min_sum;
	  free(n_count);
	  return 0;
}

int ComputeDifferenceBetweenMaxAndMinSumOfKElements_1(
 uint32_t* arr, uint32_t len, uint32_t k, uint32_t* res) {
    return ComputeDifferenceBetweenMaxAndMinSumOfKElements_0(arr, len, k, res);
}

int ComputeDifferenceBetweenMaxAndMinSumOfKElements_2(
    uint32_t* arr, uint32_t len, uint32_t k, uint32_t* res) {
    return ComputeDifferenceBetweenMaxAndMinSumOfKElements_0(arr, len, k, res);
}

int ComputeDifferenceBetweenMaxAndMinSumOfKElements_3(
    uint32_t* arr, uint32_t len, uint32_t k, uint32_t* res) {
    return ComputeDifferenceBetweenMaxAndMinSumOfKElements_0(arr, len, k, res);
}
