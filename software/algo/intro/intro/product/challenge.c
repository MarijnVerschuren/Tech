#include "challenge.h"

#include "stdio.h"


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
	
		// use sizeof
    uint32_t* n_count = calloc(m, sizeof(uint32_t));								// initialized array to count occurances for each number in "arr"
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

	  uint32_t* n_count = calloc(m, sizeof(uint32_t));												// initialized array to count occurances for each number in "arr"
	  for (uint32_t i = 0; i < len; i++) { n_count[arr[i]]++; }						// counting occurances of the numbers in "arr": O(n)
	  uint64_t min_sum = 0, max_sum = 0;
	  uint32_t min_sum_size = 0, max_sum_size = 0;
	  uint32_t current_count;
	  for (uint32_t i = 0; i < m && (min_sum_size < k || max_sum_size < k); i++) {	// find the min and max sums: O(n)
		  current_count = MIN(n_count[i], k - min_sum_size);							// calculate how many times the number i can be added to the min sum
		  if (current_count) {
			  min_sum += i * current_count;
			  min_sum_size += current_count;
		  }
		  current_count = MIN(n_count[m-i-1], k - max_sum_size);						// calculate how many times the number i can be added to the max sum
		  if (current_count) {
			  max_sum += (m-i-1) * current_count;									// +1 because we are indexing from the end of the count lookup table
			  max_sum_size += current_count;
		  }
	  }

	  *res = max_sum - min_sum;
	  free(n_count);
	  return 0;
}





uint32_t partition(uint32_t* arr, uint32_t low, uint32_t high) {
    uint32_t pivot = arr[high]; // pivot
    uint32_t i = (low  - 1); // Index of smaller element and indicates
    // the right position of pivot found so far

 		uint32_t tmp;
    for (uint32_t j = low; j <= high - 1; j++) {
        // If current element is smaller than the pivot
        if (arr[j] < pivot) {
            i++; // increment index of smaller element
            tmp = arr[j];
			arr[j] = arr[i];
			arr[i] = tmp;
        }
    }
	tmp = arr[high];
	arr[high] = arr[i + 1];
	arr[i + 1] = tmp;
	return (i + 1);
}

void quickSort(uint32_t* arr, uint32_t low, uint32_t high) {
    if (low < high) {
        /* pi is partitioning index, arr[p] is now
        at right place */
        uint32_t pi = partition(arr, low, high);
 
        // Separately sort elements before
        // partition and after partition
        quickSort(arr, low, pi - 1);
        quickSort(arr, pi + 1, high);
    }
}




void merge(uint32_t* array, uint32_t const left, uint32_t const mid,
           uint32_t const right)
{
    uint32_t const subArrayOne = mid - left + 1;
    uint32_t const subArrayTwo = right - mid;
  
    // Create temp arrays
    uint32_t	*leftArray = calloc(subArrayOne, sizeof(uint32_t)),  // new uint32_t[subArrayOne],
        		*rightArray = calloc(subArrayTwo, sizeof(uint32_t));  // new uint32_t[subArrayTwo];
  
    // Copy data to temp arrays leftArray[] and rightArray[]
    for (uint32_t i = 0; i < subArrayOne; i++)
        leftArray[i] = array[left + i];
    for (uint32_t j = 0; j < subArrayTwo; j++)
        rightArray[j] = array[mid + 1 + j];
  
    uint32_t	indexOfSubArrayOne = 0, // Initial index of first sub-array
    			indexOfSubArrayTwo = 0; // Initial index of second sub-array
    uint32_t indexOfMergedArray = left; // Initial index of merged array
  
    // Merge the temp arrays back into array[left..right]
    while (indexOfSubArrayOne < subArrayOne
           && indexOfSubArrayTwo < subArrayTwo) {
        if (leftArray[indexOfSubArrayOne]
            <= rightArray[indexOfSubArrayTwo]) {
            array[indexOfMergedArray]
                = leftArray[indexOfSubArrayOne];
            indexOfSubArrayOne++;
        }
        else {
            array[indexOfMergedArray]
                = rightArray[indexOfSubArrayTwo];
            indexOfSubArrayTwo++;
        }
        indexOfMergedArray++;
    }
    // Copy the remaining elements of
    // left[], if there are any
    while (indexOfSubArrayOne < subArrayOne) {
        array[indexOfMergedArray]
            = leftArray[indexOfSubArrayOne];
        indexOfSubArrayOne++;
        indexOfMergedArray++;
    }
    // Copy the remaining elements of
    // right[], if there are any
    while (indexOfSubArrayTwo < subArrayTwo) {
        array[indexOfMergedArray]
            = rightArray[indexOfSubArrayTwo];
        indexOfSubArrayTwo++;
        indexOfMergedArray++;
    }
    free(leftArray);
    free(rightArray);
}

void mergeSort(uint32_t* array, uint32_t const begin, uint32_t const end) {
    if (begin >= end)
        return; // Returns recursively
  
    uint32_t mid = begin + (end - begin) / 2;
    mergeSort(array, begin, mid);
    mergeSort(array, mid + 1, end);
    merge(array, begin, mid, end);
}




// Using counting sort to sort the elements in the basis of significant places
void countingSort(uint32_t* array, uint32_t size, uint32_t place) {
  uint32_t output[size + 1];
  uint32_t max = (array[0] / place) % 10;

  for (uint32_t i = 1; i < size; i++) {
    if (((array[i] / place) % 10) > max)
      max = array[i];
  }
  uint32_t count[max + 1];

  for (uint32_t i = 0; i < max; ++i)
    count[i] = 0;

  // Calculate count of elements
  for (uint32_t i = 0; i < size; i++)
    count[(array[i] / place) % 10]++;
    
  // Calculate cumulative count
  for (uint32_t i = 1; i < 10; i++)
    count[i] += count[i - 1];

  // Place the elements in sorted order
  for (uint32_t i = size - 1; i >= 0; i--) {
    output[count[(array[i] / place) % 10] - 1] = array[i];
    count[(array[i] / place) % 10]--;
  }

  for (uint32_t i = 0; i < size; i++)
    array[i] = output[i];
}

// Main function to implement radix sort
void radixsort(uint32_t* array, uint32_t size) {
  // Get maximum element
  uint32_t max = arr_max(array, size);
  // Apply counting sort to sort elements based on place value.
  for (uint32_t place = 1; max / place > 0; place *= 10)
    countingSort(array, size, place);
}





// implement sorting algorithms
// remove call to *_0 and just test sorting algorithms
int ComputeDifferenceBetweenMaxAndMinSumOfKElements_1(
 uint32_t* arr, uint32_t len, uint32_t k, uint32_t* res) {
    //return ComputeDifferenceBetweenMaxAndMinSumOfKElements_0(arr, len, k, res);
		// quicksort O(n^2)
		quickSort(arr, 0, len - 1);
		for (uint32_t i = 0; i < len; i++) {
			printf("%u", arr[i]);
		}
		return 0;
}

int ComputeDifferenceBetweenMaxAndMinSumOfKElements_2(
    uint32_t* arr, uint32_t len, uint32_t k, uint32_t* res) {
    //return ComputeDifferenceBetweenMaxAndMinSumOfKElements_0(arr, len, k, res);
		// merge sort O(n log n)
		mergeSort(arr, 0, len - 1);
		for (uint32_t i = 0; i < len; i++) {
			printf("%u", arr[i]);
		}
		return 0;
}

int ComputeDifferenceBetweenMaxAndMinSumOfKElements_3(
    uint32_t* arr, uint32_t len, uint32_t k, uint32_t* res) {
    //return ComputeDifferenceBetweenMaxAndMinSumOfKElements_0(arr, len, k, res);
	  	// radix sort O(nk)
		radixsort(arr, len);
		for (uint32_t i = 0; i < len; i++) {
			printf("%u", arr[i]);
		}
		return 0;
}
