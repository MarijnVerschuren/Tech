#ifndef TIMECONSTANTS_H
#define TIMECONSTANTS_H

#define MIN *60000

struct Time {
	uint32_t time = 0;
	uint32_t max_time = 0;
	uint32_t additional_time = 0;

	Time() = default;
	Time(uint32_t t) {
		time = t;
		max_time = t;
		additional_time = 0;
	}
	Time(uint32_t t, uint32_t t_max) {
		time = t;
		max_time = t_max;
		additional_time = 0;
	}
	void get(uint32_t& hours, uint32_t& minutes) const {
		hours = (time + additional_time) / 60;
		minutes = (time + additional_time) % 60;
	}
	void get_max(uint32_t& hours, uint32_t& minutes) const {
		hours = (max_time + additional_time) / 60;
		minutes = (max_time + additional_time) % 60;
	}
};

const Time rest_times[] = {
		{60},
		{60},
		{0},
		{40},
		{0xffffffff}  // none
};
const Time knead_times[] = {
		{20},
		{20},
		{15},
		{20},
		{0xffffffff}  // none
};
const Time rise_times[] = {
		{160},
		{160},
		{60},
		{80},
		{0xffffffff}  // none
};
const Time bake_times[] = {
		{50},
		{50},
		{40},
		{0xffffffff},  // none
		{30, 90}
};
const Time total_times[] = {
		{290},
		{290},
		{115},
		{140},
		{30, 90}
};

#endif
