#include <stdio.h>
#include <time.h>
/* 1st part of Assignment 1 SD */


int main() {
	/* this is code to measure the time of your algorithm, please don't touch it */

    	clock_t t; 
	double time_taken;

    	t = clock(); 
  
	/* read here the stdin to get the values of N, a1...an 
	 * and store them
	 *
	 * for this you can use scanf e.g. like this:
	 *
	 * int n;
	 * scanf("%d", &n);
	 */


	/* implement her your code e.g. like this 
	 * ret = get_smaller_numbers( choose your own arguments );
	 */


	/* this is the (performance) test code, please don't touch it */

	t = clock() - t;
	time_taken = ((double)t)/CLOCKS_PER_SEC;
	printf("The result numbers are \n");
	/*
	 * use loop to print your array in this format
	 *	printf("%d \n", outcome_arr[i]);
	 */
	printf("\n");
#ifdef TEST_TIME
	printf("time needed was %f seconds\n", time_taken);
#endif
	return 0;
}
