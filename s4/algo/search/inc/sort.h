#ifndef SORT_SORT_H
#define SORT_SORT_H

#include "defs.h"


// a < b	-> -1
// a == b	-> 0
// a > b	-> 1
int8_t compare_words(const str a, const str b) {
	char ac, bc;
	for (uint8_t i = 0; ac = *(a + i), bc = *(b + i), ac && bc; i++) {
		if (ac < bc) { return -1; }
		if (bc < ac) { return 1; }
	}
	if (!ac && bc) { return -1; }
	if (!bc && ac) { return 1; }
	return 0;
}
extern int8_t cmp_words(const str a, const str b);  // TODO: in assembly


typedef int8_t (*comp_fn) (const void*, const void*);
extern void bubble_sort(void* array, uint64_t size, comp_fn comp);


#endif //SORT_SORT_H
