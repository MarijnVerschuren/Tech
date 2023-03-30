#include "MemoryManager.h"
#include "MList.h"
#include <iostream>

using namespace std;

/* Starting point for MemoryManager constructor */
MemoryManager::MemoryManager()
{
	allocList = new AllocList(memStart, maxSize);
	freeList = new FreeList(memStart, maxSize);
}

/* Code correct destructor to cleanup all memory */
MemoryManager::~MemoryManager()
{
}

/* pre : size > 0
 * post: If no memory block of size "size" available return -1
 *       Otherwise claimMemory() returns the first
 *       address in the freeList where a memory block of at least size is present.
 *       This memory is allocated and not any more available.
 *       The newly allocated block is added to the allocList and addr of the newly
 *       allocated block is returned
 */

int MemoryManager::claimMemory(int size)
{
	return -1;
}

/* pre:  Parameter addr must match the start of an allocatd memory block. Otherwhise return -1.
 *
 * post: If addr is a part of allocated memory of allocList then the memory from this address
 * 	     with registered size should be removed from the allocList and added to the freeList
 *
 *       freeMemory(addr) returns number of bytes (size) belongig to the address addr
 *       In all other cases freeMemory(freeList,allocList,addr) returns -1.
 */


int MemoryManager::freeMemory(int addr)
{
	return -1;
}

