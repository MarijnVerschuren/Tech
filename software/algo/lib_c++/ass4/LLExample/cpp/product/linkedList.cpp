#include "linkedList.h"
#include <iostream>


int linkedList::addFirst(int value) {
	item *it = new item;
	it->value = value;
	if(head == 0)
	{
		head = it;
		tail = it;
	}
	else
	{
		it->next = head;
		head = it;
	}
	return 0;
}
	
void linkedList::showList() {
	std::cout << "[";
	for(item *it=head; it!=0; it=it->next) {
		std::cout << it->value;
		if (it->next != nullptr) { std::cout << ", "; }
	}
	std::cout << "]\n";
}

int linkedList::getHeadValue()
{
	return head->value;
}

int linkedList::getTailValue()
{
	return tail->value;
}
