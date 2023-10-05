#ifndef SEARCH_SEACH_H
#define SEARCH_SEACH_H

#include <malloc.h>
#include <string.h>

#include "defs.h"


uint64_t text_to_words(str text, str** words) {
	uint64_t word_count = 0, i = 0, j = 0, k = 0;
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
			(*words)[j] = calloc(sizeof(char), i);
			memcpy((*words)[j], text, i - 1);
			text += i; j++;
		}
	}

	return word_count;
}


extern uint64_t linear_count(const str text, const str word);
extern uint64_t linear_count_a(const str* words, uint64_t size, const str word);
extern uint64_t binary_count_a(const str* words, uint64_t size, const str word);


#endif //SEARCH_SEACH_H