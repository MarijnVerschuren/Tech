#ifndef SEARCH_SEACH_H
#define SEARCH_SEACH_H

#include <malloc.h>
#include <string.h>

#include "defs.h"
#include "sort.h"


uint64_t text_to_words(str text, str** words, uint8_t pad_to) {
	uint64_t word_count = 0, i = 0, j = 0, k;
	uint64_t word_size;
	uint8_t read = 0;

	do {
		if (*(text + i) == 0x20 || !*(text + i)) { word_count += read; read = 0; }
		else { read = 1; }
	} while (*(text + i++));

	*words = malloc(sizeof(void *) * word_count);

	while (*(text++)) {
		for (i = 0; *(text + i) && *(text + i++) != 0x20;);
		k = !*(text + i);  // create flag that will be added to i because i is in this case not incremented during the for loop check
		if (i) {
			text--; i = i + 1 + k;  // text alignment
			word_size = i;
			if (pad_to) { word_size += pad_to - (word_size % pad_to); }
			(*words)[j] = calloc(sizeof(char), word_size);
			memcpy((*words)[j], text, i - 1);
			text += i; j++;
		} if (k) { break; }
	}

	return word_count;
}


extern uint64_t linear_count(const str* words, uint64_t size, const str word, comp_fn comp);
extern uint64_t binary_count(const str* words, uint64_t size, const str word, comp_fn comp);


#endif //SEARCH_SEACH_H