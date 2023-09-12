#pragma once

#include <stdint.h>


typedef struct ITEM {
	struct ITEM* next = nullptr;
	struct ITEM* prev = nullptr;
    int _addr = 0;
    int _size = 0;
    ITEM(int addr, int size) {_addr=addr; _size=size;}
} ITEM;

typedef int8_t (*cmp_func)(ITEM, ITEM);
int8_t cmp_ITEM_addr(ITEM, ITEM);

typedef enum {
	ok =				0x00,
	empty =				0x01,
	index_error =		0x10,
	allocation_error =	0x20,
} Status;

class MList {  // i did not want to implement list AGAIN... (and std::list sucks)
private:
	ITEM* head = nullptr;
	ITEM* tail = nullptr;
	uint64_t length = 0;

	ITEM* index(uint64_t index);
	void disconnect();  // disconnect nodes without deletion
public:
	MList() = default;
	~MList();
	uint64_t get_length() { return this->length; }

	void clear();
	ITEM& operator[](uint64_t index);
	uint64_t find(ITEM data, cmp_func cmp = cmp_ITEM_addr);
	uint64_t rfind(ITEM data, cmp_func cmp = cmp_ITEM_addr);

	Status append(ITEM data);
	Status insert(ITEM data, uint64_t index);
	Status pop();
	Status remove(uint64_t index);

	MList split(uint64_t index);
	Status extend(MList* src);					// deletes src
	Status insert(MList* src, uint64_t index);	// deletes src

	friend void MList_sort(MList* list, cmp_func cmp);
	friend void print(MList* list);
};


void MList_sort(MList* list, cmp_func cmp = cmp_ITEM_addr);
void print(MList* list);
