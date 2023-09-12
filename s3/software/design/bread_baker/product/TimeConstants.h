#ifndef TIMECONSTANTS_H
#define TIMECONSTANTS_H

#define MIN *60000
#define MS *1000
#define TIME_REPR(x, h, m) do { \
    	(h) = (int)((x) / 60);  \
    	(m) = 	   ((x) % 60);  \
	} while (0)
// TODO: time to hours, minutes converter

const int rest_times[] = {
		60,
		60,
		0,
		40,
		-1  // none
};
const int knead_times[] = {
		20,
		20,
		15,
		20,
		-1  // none
};
const int rise_times[] = {
		160,
		160,
		60,
		80,
		-1  // none
};
const int bake_times[] = {
		50,
		50,
		40,
		-1,  // none
		30
};
const int yeast_times[] = {
		10,
		10,
		8,
		10,
		-1  // none
};
const int extra_times[] = {
		-1,
		15,
		-1,
		-1,
		-1  // none
};
const int total_times[] = {
		290,
		290,
		115,
		140,
		30
};

#endif
