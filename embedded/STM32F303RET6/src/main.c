#include "main.h"
#include "gpio.h"	// all pins are defined here
#include "nvic.h"
#include "tim.h"	// all timers and delays are defined here


void EXTI15_10_IRQHandler(void) {
	if(EXTI->PR & (1 << BTN_PIN)) {
		EXTI->PR |= (1 << BTN_PIN);	// clear interrupt bit
		toggle_pin(LED_PIN, LED_GPIO_PORT);
	}
}


int main(void) {
	GPIO_init();  // initialize GPIO peripheral clock (on enabled ports)
	NVIC_init();
	enable_EXTI(BTN_PIN, BTN_GPIO_PORT, 1, 1);

	pin_init(LED_PIN, LED_GPIO_PORT, GPIO_output, GPIO_medium_speed, GPIO_no_pull);
	set_pin_config(BTN_PIN, BTN_GPIO_PORT, 0, GPIO_pull_up);  // set btn pull-up
	NVIC_EnableIRQ(EXTI15_10_IRQn);  // TODO: add this in enable EXTI somehow

	while (1) {
	}
	// TODO: Fix flickering of the led (irq handler)
}