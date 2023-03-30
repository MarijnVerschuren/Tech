#include <stdio.h>
static int sum(int *a, int n)
{
	int sum=0;
	for(int i=0; i< n; i++)
	{
		sum += a[i];
		i--;
	}
	return sum;
}

void main()
{
	const int n = 5;
	const int m = 2;
	
	int arr[n];
	int mat[n][m];

	for(int i=0; i<n; i++)
	{
		arr[i]=-1;
		for(int j=0; j<n; j++)
		{
			mat[i][j]=i*j;
		}
	}

	int s = sum(arr,n);
	printf("sum is %d\n", s);
}
