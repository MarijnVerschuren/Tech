#include <iostream>

#include "../inc/cantcoap.h"
#include <arpa/inet.h>
#include "../inc/dbg.h"


int main() {
	CoapPDU conn = CoapPDU();
	std::cout << conn.getOptions()->optionNumber << std::endl;
	return 0;
}
