#ifndef TIMECONSTANTS_H
#define TIMECONSTANTS_H

#define MIN *60000


const uint32_t rest_times[] = {
		60,
		60,
		0,
		40,
		0xffffffff  // none
};
const uint32_t knead_times[] = {
		20,
		20,
		15,
		20,
		0xffffffff  // none
};
const uint32_t yeast_times[] = {
		10,
		10,
		8,
		10,
		0xffffffff  // none
};
const uint32_t extra_times[] = {
		0xffffffff,
		15,
		0xffffffff,
		0xffffffff,
		0xffffffff  // none
};
const uint32_t rise_times[] = {
		160,
		160,
		60,
		80,
		0xffffffff  // none
};
const uint32_t bake_times[] = {
		50,
		50,
		40,
		0xffffffff,  // none
		30
};
const uint32_t total_times[] = {
		290,
		290,
		115,
		140,
		30
};

#endif
