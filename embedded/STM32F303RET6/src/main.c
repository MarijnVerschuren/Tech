#include "main.h"
#include "gpio.h"	// all pins are defined here
#include "exti.h"
#include "tim.h"	// all timers and delays are defined here


volatile uint8_t state = 0;
extern void EXTI15_10_IRQHandler(void) {
	// handle interrupt here
	if(EXTI->PR & (1 << BTN_PIN)) {
		EXTI->PR = EXTI_PR_PR13;
		// EXTI->PR &= ~(1 << BTN_PIN);	// clear interrupt bit
		write_pin(LED_PIN, LED_GPIO_PORT, !read_pin(LED_PIN, LED_GPIO_PORT));
	}
}


int main(void) {
	GPIO_init();  // initialize GPIO peripheral clock (on enabled ports)
	EXTI_init();
	enable_EXTI(BTN_PIN, BTN_GPIO_PORT, 1, 0);

	pin_init(LED_PIN, LED_GPIO_PORT, GPIO_output, GPIO_medium_speed, GPIO_no_pull);
	pin_init(BTN_PIN, BTN_GPIO_PORT, GPIO_input, GPIO_medium_speed, GPIO_pull_up);  // set btn pull-up
	NVIC_EnableIRQ(EXTI15_10_IRQn);  // TODO: add this in enable EXTI somehow

	while (1) {
		//write_pin(LED_PIN, LED_GPIO_PORT, read_pin(BTN_PIN, BTN_GPIO_PORT));
	}
	// TODO: Fix flickering of the led (irq handler)
}