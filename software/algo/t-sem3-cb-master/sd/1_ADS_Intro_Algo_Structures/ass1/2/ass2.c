#include <stdio.h>
#include <time.h>
/* 2nd part of Assignment 1 SD */


int main() {
	/* this is code to measure the time of your algorithm, please don't touch it */

    	clock_t t; 
	double time_taken;

    	t = clock(); 
  
	/* read here the stdin to get the values of N, a1...an and K
	 * and store them
	 *
	 * for this you can use scanf e.g. like this:
	 *
	 * int n;
	 * scanf("%d", &n);
	 */

	int outcome=0;

	/* implement her your code e.g. like this 
	 * outcome = get_difference_between_min_and_max_sum_of_k_elems( choose your own arguments );
	 */


	/* this is the (performance) test code, please don't touch it */

	t = clock() - t;
	time_taken = ((double)t)/CLOCKS_PER_SEC;
	printf("difference between minimum and maximum sum of K elements is %d\n", outcome);
#ifdef TEST_TIME
	printf("time needed was %f seconds\n", time_taken);
#endif
	return 0;
}
