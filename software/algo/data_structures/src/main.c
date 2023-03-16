#include "list.h"
#include "../inc/list.h"  // this is done so that the ide can find the header file


void print_str_list(List* list) {
	for (uint64_t i = 0; i < list->length; i++) {
		printf("%lu: %s\n", i, *((const char**)list_index(list, i)));
	}
	printf("\n");
}

void print_str_node(Node* node, const char* name) {
	printf("node: %p %s\n\tnext: %p\n\tprev: %p\n", node, name, node->next, node->prev);
}

void print_str_nodes(List* list) {
	Node* node = list->head;
	for (uint64_t i = 0; i < list->length; i++) {
		if (node == list->head) { print_str_node(node, "(head)"); }
		else if (node == list->tail) { print_str_node(node, "(tail)"); }
		else { print_str_node(node, ""); }
		node = node->next;
	}
}



int main() {
	List* list = new_list(sizeof(const char*));
	// strings are defined in the binary so do not have to be freed
	// but the ability to define your custom data deletion function is added to the list

	const char* text_0 = "hello list";
	const char* text_1 = "list index 1";
	const char* text_2 = "list index 2";
	const char* text_3 = "list index 3";
	const char* text_4 = "list index 4";
	list_append(list, &text_0);
	list_append(list, &text_1);
	list_append(list, &text_2);
	list_append(list, &text_3);
	list_append(list, &text_4);

	//print_str_list(list);
	//print_str_nodes(list);

	const char* text_insert = "list insert";
	list_insert(list, &text_insert, 3);

	//print_str_list(list);
	//print_str_nodes(list);

	list_pop(list);
	list_remove(list, 2);

	print_str_list(list);
	//print_str_nodes(list);

	List* list2 = split_list(list, 2);

	print_str_list(list);
	print_str_list(list2);

	return 0;
}
