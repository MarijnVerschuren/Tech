#ifndef PROGRAM_H
#define PROGRAM_H

struct Program {
	int delay;		// delay added to resting stage
    int waiting;
    int kneading;
    int rising;
    int baking;
	int yeast;
	int extras;
	int total_time;

	int kneading_cycles;
};

enum Program_Type {
	BREAD_PLAIN =	0,
	BREAD_PLUS =	1,
	RAPID =			2,
	DOUGH =			3,
	BAKE =			4
};
#define PROGRAM_COUNT 5
#define MAX_OVEN_TEMP 50



#endif
