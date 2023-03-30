// Sample code to perform I/O:
#include <stdio.h>
#include <stdlib.h>

typedef struct Node {
	int data;
	struct Node *next;
}Node;

int main(){
	int num;
	int value;
	Node *list;

	scanf("%d", &num);         
	
	for(int i=0; i< num; i++)
	{
		scanf("%d", &value);
	/* 	add here your own code to create a list from the provided values, e.g.
		add_last(&list, value); */
	}

	/* your code */
	
	/* Use this code to print the final values	
	Node *temp = list;
	while(temp)
	{
		printf("%d ", temp->data);
		temp = temp->next;
	}
	*/

	/* Don't forget to clean the memory
	   clean_list(&list); */
}

