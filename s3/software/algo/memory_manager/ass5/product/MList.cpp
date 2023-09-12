#include <iostream>
#include "MList.h"


static void del_node(ITEM* item) {
	if (!item) { return; }
	if (item->next) { del_node(item->next); }
	delete item;
}


int8_t cmp_ITEM_addr(ITEM a, ITEM b) {
	return a._addr > b._addr ? 1 : a._addr < b._addr ? -1 : 0;
}

MList::~MList() { this->clear(); }

void MList::clear() {
	del_node(this->head);
	this->disconnect();
}

ITEM* MList::index(uint64_t index) {
	if (index >= this->length) { return nullptr; }
	ITEM* item = this->head;
	while (index-- && item) { item = item->next; }
	return item;
}

void MList::disconnect() {
	this->head = nullptr;
	this->tail = nullptr;
	this->length = 0;
}

ITEM& MList::operator[](uint64_t index) {
	const ITEM* item = this->index(index);
	if (!item) { item = new ITEM(0, 0); }  // return empty item on error
	return const_cast<ITEM &>(*item);
}

uint64_t MList::find(ITEM data, cmp_func cmp) {
	ITEM* item = this->head;
	uint64_t index = this->length - 1;
	while (index-- && item) {
		if (!cmp(*item, data)) { return (this->length - 1) - index; }
		item = item->next;
	}
	return -1;
}

uint64_t MList::rfind(ITEM data, cmp_func cmp) {
	ITEM* item = this->tail;
	uint64_t index = this->length - 1;
	while (index-- && item) {
		if (!cmp(*item, data)) { return index; }
		item = item->prev;
	}
	return -1;
}

Status MList::append(ITEM data) {
	ITEM* node = new ITEM(data._addr, data._size);
	if (!this->tail || !this->head) {
		this->head = node;
		this->tail = node;
		this->length = 1;
		return ok;
	}
	this->tail->next = node;
	node->prev = this->tail;
	this->tail = node;
	this->length++;
	return ok;
}

Status MList::insert(ITEM data, uint64_t index) {
	ITEM* node = this->index(index);
	if (!node) { return index_error; }
	ITEM* prev = node->prev;
	ITEM* next = new ITEM(data._addr, data._size);
	next->next = node;
	next->prev = prev;
	node->prev = next;
	if (prev)	{ prev->next = next; }
	else		{ this->head = next; }
	this->length++;
	return ok;
}

Status MList::pop() {
	if (!this->length) { return empty; }
	ITEM* prev = this->tail->prev;
	delete this->tail;
	if (prev) { prev->next = nullptr; }
	else { this->head = nullptr; }
	this->tail = prev;
	this->length--;
	return ok;
}

Status MList::remove(uint64_t index) {
	if (index == this->length - 1)	{ return this->pop(); }
	ITEM* item = this->index(index);
	if (!item) { return index_error; }
	ITEM* prev = item->prev;
	ITEM* next = item->next;
	if (prev) { prev->next = next; }
	if (next) { next->prev = prev; }
	if (item == this->head) {
		this->head = next;
	}
	delete item;
	this->length--;
	return ok;
}

MList MList::split(uint64_t index) {
	MList ret;
	ITEM* node = this->index(index);
	if (!node) { return ret; }
	ret.length = this->length - index;
	this->length = index;
	ret.head = node;
	ret.tail = this->tail;
	this->tail = node->prev;
	this->tail->next = nullptr;
	ret.head->prev = nullptr;
	return ret;
}

Status MList::extend(MList* src) {
	ITEM* end = this->tail;
	this->tail = src->tail;
	src->head->prev = end;
	end->next = src->head;
	this->length += src->length;
	src->head = nullptr;
	src->tail = nullptr;
	src->length = 0;
	return ok;
}

Status MList::insert(MList* src, uint64_t index) {
	ITEM* next = this->index(index);
	if (!next) { return index_error; }
	ITEM* prev = next->prev;
	prev->next = src->head;
	src->head->prev = prev;
	next->prev = src->tail;
	src->tail->next = next;
	this->length += src->length;
	src->head = nullptr;
	src->tail = nullptr;
	src->length = 0;
	return ok;
}


void MList_sort(MList* list, cmp_func cmp) {
	uint64_t length = list->length;
	if (length <= 1) { return; }
	MList b = list->split(length >> 1);
	MList_sort(list,	cmp);
	MList_sort(&b,		cmp);
	MList tmp;
	uint64_t i = 0, j = 0;
	for (; (i < list->length) && (j < b.length);) {
		if (cmp((*list)[i], b[j]) < 1) {  // a[i] <= b[j]
			tmp.append((*list)[i]);
			i++; continue;
		} tmp.append(b[j]); j++;
	}
	for (; i < list->length; i++) { tmp.append((*list)[i]); }
	for (; j < b.length; j++) { tmp.append(b[j]); }
	list->head = tmp.head;
	list->tail = tmp.tail;
	list->length = tmp.length;
	b.disconnect();
	tmp.disconnect();
}

void print(MList* list) {
	std::cout << "<len=" << list->length << ", head=" << std::hex << list->head << ", tail=" << std::hex << list->tail << ", {\n";
	for (uint64_t i = 0; i < list->length; i++) {
		std::cout << "\t<ptr=" << std::hex << &(*list)[i] << ", next=" << std::hex << (*list)[i].next << ", prev=" << std::hex << (*list)[i].prev << ", addr=" << std::dec << (*list)[i]._addr << ", size=" << std::dec << (*list)[i]._size << ">\n";
	}
	std::cout << "}>\n" << std::dec;
}

/* Implementation of all your MList methods */
