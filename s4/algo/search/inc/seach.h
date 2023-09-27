#ifndef SEARCH_SEACH_H
#define SEARCH_SEACH_H

#include "defs.h"



typedef struct {
	void*	child;
	str		word;
} binary_tree;


binary_tree text_to_tree(const str text) {
	binary_tree tree = {};
	// TODO:
	return tree;
}

extern uint64_t linear_search(const str text, const str word);
extern uint64_t binary_search(binary_tree* tree, const str word);


#endif //SEARCH_SEACH_H


/*uint64_t linear_search_c(const str text, const str word) {
	uint64_t count = 0;
	uint64_t index = 0;
	uint64_t word_len = strlen(word);
	char a, b;

	do {
		a = *text++;
		b = *(word + index);
		index++;
		if (a != b) {
			if (index > 1) { text--; }
			index = 0;
		}
		if (!b) {
			index = 0;
			count++;
		}
	} while (a);
	return count;
}*/