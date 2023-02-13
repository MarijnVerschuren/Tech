//
// Created by marijn on 2/13/23.
//
#include "tim.h"


void ms_delay(uint32_t ms) {
	while (ms-- > 0) {
		uint32_t x = 500;
		while (x-- > 0)
			__asm("nop");
	}
}