#include "linkedList.h"
#include <iostream>

using namespace std;

int linkedList::addFirst(int value)
 {
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
	
void linkedList::showList()
{
	cout << "List elements are \n";
	
	for(item *it=head; it!=0; it=it->next)
	{
		cout << it->value << endl;
	}
}

int linkedList::getHeadValue()
{
	return head->value;
}

int linkedList::getTailValue()
{
	return tail->value;
}
