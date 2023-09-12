//
// Created by marijn on 3/16/23.
//

#ifndef DATA_STRUCTURES_MAIN_H
#define DATA_STRUCTURES_MAIN_H

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define nullptr ((void*)0)

/*!< errors
 * \n 0x00 - 0x0f: soft error
 * \n 0x10 - 0xf0: hard fault */
typedef enum {
	ok =				0x00,
	empty =				0x01,
	index_error =		0x10,
	allocation_error =	0x20,

} Status;

#endif //DATA_STRUCTURES_MAIN_H
