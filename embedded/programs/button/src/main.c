#include "main.h"
#include "gpio.h"	// all pins are defined here
#include "tim.h"	// all timers and delays are defined here


int main(void) {
	GPIO_init();  // initialize GPIO peripheral clock (on enabled ports)
	pin_init(LED_PIN, LED_GPIO_PORT, GPIO_output, GPIO_medium_speed, GPIO_no_pull);
	pin_init(BTN_PIN, BTN_GPIO_PORT, GPIO_input, GPIO_medium_speed, GPIO_pull_up);

	while (1) {
		write_pin(LED_PIN, LED_GPIO_PORT, read_pin(BTN_PIN, BTN_GPIO_PORT));
		//toggle_pin(LED_PIN, LED_GPIO_PORT);
		//ms_delay(500);
	}
}