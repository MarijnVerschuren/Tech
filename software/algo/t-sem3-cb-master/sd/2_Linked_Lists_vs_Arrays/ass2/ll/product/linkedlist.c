/* SD exercise 1: simple linked list API */
/* Author : R. Frenken                   */
/* Version : 1.0			 */
#include "linkedlist.h"
#include <stdlib.h>

/***************************************************/
/* If *list == NULL, a new list should be created, */
/* otherwise prepend a new ITEM with value value   */
/* to the existing list                            */
/* Returns -1 if not enough memory, otherwise 0    */
/***************************************************/

int add_first(ITEM **list, int value)
{
	/* Implement */
	return 0;
}

/***************************************************/
/* If *list == NULL, a new list should be created, */
/* otherwise append a new ITEM with value value to */
/* the existing list                               */
/* Returns -1 if not enough memory, otherwise 0    */
/***************************************************/

int add_last(ITEM **list, int value)
{
	/* Implement */
	return 0;
}

/****************************************************/
/* Insert a new item after current item c_item      */
/* Returns -1 if not enough memory, c_item == NULL, */
/* *list == NULL or c_item not found, otherwise 0   */
/****************************************************/

int add_after(ITEM *list, ITEM *c_item, int value)
{
	/* Implement */
	return 0;
}


/***************************************************/
/* Remove first item of the list                   */
/* Returns -1 if list==NULL, otherwise 0           */
/***************************************************/

int rem_first(ITEM **list)
{
	/* Implement */
	return 0;
}

/***************************************************/
/* Remove last item of the list                    */
/* Returns -1 if list==NULL, otherwise 0           */
/***************************************************/


int rem_last(ITEM **list)
{
	/* Implement */
	return 0;
}

/***************************************************/
/* Remove item after c_item of the list            */
/* Returns -1 list==NULL, c_item not found or      */
/* c_item is the last_element                      */
/***************************************************/

int rem_after(ITEM *list, ITEM *c_item)
{
	/* Implement */
	return 0;
}

/*********************************************************/
/* All dynamic memory allocated to the list is freed     */
/* Empty list should point to NULL                       */
/*********************************************************/

void clean(ITEM **list)
{
	/* Implement */
	return;
}

