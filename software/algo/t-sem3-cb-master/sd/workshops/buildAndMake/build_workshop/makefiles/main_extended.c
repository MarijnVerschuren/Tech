#include "header.h"
#include "header2.h"
#include <stdio.h>
#define NR_OF_ELEMS 30

extern int my_function1();
extern int my_function2();
extern int my_function3();


int main()
{
	printf("Let's do some make experiments !\n");
	my_function1();
	my_function2();
	my_function3();
	return 0;
}
