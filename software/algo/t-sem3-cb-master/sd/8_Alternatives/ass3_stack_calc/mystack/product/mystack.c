#include "mystack.h"
#include "logging.h"
/* The stack is an abstract data type.
 * this means that the internal structures are
 * never exposed to the users of the library.
 */

/* Note: the stacks have no knowledge of what types
 * they are storing. This is not a concern of the stack
 */

typedef struct stackObject* pStackObject_t;
typedef struct stackObject
{
	void* obj;
	pStackObject_t next;
} StackObject_t;

typedef struct stackMEta* pStackMeta_t;
typedef struct stackMEta
{
	pStackObject_t stack;
	size_t objsize;
	int numelem;
	int handle;
	pStackMeta_t next;
} StackMeta_t;

static pStackMeta_t gStackList = NULL;

 int mystack_create(size_t objsize)
 {
 	/* Hint: use gStackList */
 	int handle = 1;
 	DBG_PRINTF("Created stack with handle: %d and objsize %zu bytes\n", handle, objsize);
 	return 0;
 }
 
 int mystack_push(int handle, void* obj)
 {
    DBG_PRINTF("handle: %d\n, obj: %p\n", handle, obj); 	
 	return 0;
 }

 int mystack_pop(int handle, void* obj)
 {
    DBG_PRINTF("handle: %d\n, obj: %p\n", handle, obj); 	
 	return 0;
 }

 int mystack_destroy(int handle)
 {
    DBG_PRINTF("handle: %d\n", handle); 	
 	return 0;
 }

 int mystack_nofelem(int handle)
 {
    DBG_PRINTF("handle: %d\n", handle);
 	return 0;
 }


