#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "challenge.h"

int main(int argc, char* argv[])
{
    if (argc != 2)
    {
        printf("Please provide argument to select assignment.\n");
        return -1;
    }
    char selectedAssignment = atoi(argv[1]);

    
    uint32_t len = 0;
    scanf("%u", &len);
	
    if (!len) { return -1; }										// you cant have an array of size 0
    uint32_t* arr = malloc(len * 4);								// uninitialzed array for numbers (these will be set)
    for (uint32_t i = 0; i < len; i++) { scanf("%u ", &arr[i]); }	// set array indecies with data from stdin
	
    uint32_t k = 0;
    scanf("%u", &k);
    
    if (selectedAssignment == 1)
    {
        uint32_t smallestNumber = 0;
        FindSmallestNumberThatIsRepeatedKTimes(arr, len, k, &smallestNumber);

        printf("%d\n", smallestNumber);
    }
    else if (selectedAssignment == 2)
    {
        uint32_t difference = 0;
        ComputeDifferenceBetweenMaxAndMinSumOfKElements_0(arr, len, k, &difference);

        printf("%d\n", difference);
    }
    else if (selectedAssignment == 31)
    {
        uint32_t difference = 0;
        ComputeDifferenceBetweenMaxAndMinSumOfKElements_1(arr, len, k, &difference );
        printf("%d\n", difference);
    }
    else if (selectedAssignment == 32)
    {
        uint32_t difference = 0;
        ComputeDifferenceBetweenMaxAndMinSumOfKElements_2(arr, len, k, &difference);
        printf("%d\n", difference);
    }
    else if (selectedAssignment == 33)
    {
        uint32_t difference = 0;
        ComputeDifferenceBetweenMaxAndMinSumOfKElements_3(arr, len, k, &difference);
        printf("%d\n", difference);
    }
    else
    {
        printf("Error: Unknown assignment: %d\n", selectedAssignment);
    }

    return 0;
}
