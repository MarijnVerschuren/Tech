// CPP Program to implement merge sort using
// multi-threading

#include <cstdio>
#include <iostream>
#include <fstream>
#include <vector>
#include <time.h>
#include <cstring>
#include <iostream>
#include <thread>
#include <pthread.h>

using namespace std;
#define MAX1 10000
int arr[MAX1];

static void read_in_arrays_to_sort(int *arr, int n)
{
	for (int i = 0; i < n; i++)
	{
		scanf("%d", &arr[i]);
	}
}

static void write_to_file(int *arr, int n, const string filename)
{
	ofstream f;
	f.open(filename);

	for (int i = 0; i < n; i++)
	{
		f << arr[i] << " ";
	};
	f << endl;
	f.close();
}


static void copy_input_arrays(int *arr, int *sarr, int n)
{
	memcpy(arr, sarr, n * sizeof(int));
}


int main()
{
	int sarr[MAX1];

	read_in_arrays_to_sort(sarr, MAX1);
	copy_input_arrays(arr, sarr, MAX1);

	clock_t t;
	t = clock();

	/* your implementation should come here */

	t = clock() - t;
	cout << "Time needed to sort " << MAX1 << " elements was "<< (float) t/CLOCKS_PER_SEC << "seconds" << endl;

	write_to_file(arr, MAX1, "out_alg");

	return 0;
}
