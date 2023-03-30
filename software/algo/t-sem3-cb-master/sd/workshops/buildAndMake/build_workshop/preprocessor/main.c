#include "header.h"
#include "header2.h"
#include <stdio.h>
#define NR_OF_ELEMS 30

int main()
{
	ELEM my_elem;
	my_elem->value = 1;
	my_elem->next = NULL;

	printf("Let's do some preprocessor experiments !\n");
#ifdef DEBUG
	printf("Passed nr %d\n", NR_OF_ELEMS);
#endif
#if DEBUG==2
	printf("Now I want even more debug\n");
#endif
}
