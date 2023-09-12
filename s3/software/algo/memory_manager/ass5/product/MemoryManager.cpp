#include "MemoryManager.h"
#include "MList.h"
#include <iostream>
#include <stdint.h>


using namespace std;

/* Starting point for MemoryManager constructor */
MemoryManager::MemoryManager() {
	allocList = new AllocList(memStart, maxSize);
	freeList = new FreeList(memStart, maxSize);
	freeList->append(ITEM(memStart, maxSize));
}

/* Code correct destructor to cleanup all memory */
MemoryManager::~MemoryManager() {
	delete allocList;
	delete freeList;
}

/* pre : size > 0
 * post: If no memory block of size "size" available return -1
 *       Otherwise claimMemory() returns the first
 *       address in the freeList where a memory block of at least size is present.
 *       This memory is allocated and not any more available.
 *       The newly allocated block is added to the allocList and addr of the newly
 *       allocated block is returned
 */

int MemoryManager::claimMemory(int size) {
	if (size <= 0) { return -1; }
	uint32_t i = 0;
	for (; i < freeList->get_length(); i++) {
		if ((*freeList)[i]._size >= size) { break; }
	}
	if (i == freeList->get_length()) { return -1; }
	int addr = (*freeList)[i]._addr;
	(*freeList)[i]._size -= size;
	(*freeList)[i]._addr += size;
	allocList->append(ITEM(addr, size));
	if (!(*freeList)[i]._size) { freeList->remove(i); }

	MList_sort(allocList);
	MList_sort(freeList);
	return addr;
}

/* pre:  Parameter addr must match the start of an allocatd memory block. Otherwhise return -1.
 *
 * post: If addr is a part of allocated memory of allocList then the memory from this address
 * 	     with registered size should be removed from the allocList and added to the freeList
 *
 *       freeMemory(addr) returns number of bytes (size) belongig to the address addr
 *       In all other cases freeMemory(freeList,allocList,addr) returns -1.
 */
int MemoryManager::freeMemory(int addr) {
	uint32_t i = 0;
	for (; i < allocList->get_length(); i++) {
		if ((*allocList)[i]._addr == addr) { break; }
	}
	if (i >= allocList->get_length()) { return -1; }
	int size = (*allocList)[i]._size;
	if (size) {
		freeList->append((*allocList)[i]);
		allocList->remove(i);
	}

	idc:
	for (uint32_t i = 0; i < freeList->get_length(); i++) {
		for (uint32_t j = 0; j < freeList->get_length(); j++) {
			if (!(*freeList)[i]._size || !(*freeList)[j]._size) { continue; }
			if ((*freeList)[i]._addr + (*freeList)[i]._size == (*freeList)[j]._addr) {
				(*freeList)[i]._size += (*freeList)[j]._size;
				freeList->remove(j);
				goto idc;
			}
		}
	}

	MList_sort(allocList);
	MList_sort(freeList);
	return size;
}