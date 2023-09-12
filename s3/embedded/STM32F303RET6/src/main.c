#include "main.h"
#include "gpio.h"	// all pins are defined here
#include "exti.h"
#include "tim.h"	// all timers and delays are defined here


extern void EXTI15_10_IRQHandler(void) {
	if(EXTI->PR & EXTI_PR_PR13) {
		EXTI->PR = EXTI_PR_PR13;  // clear interrupt pin (write to it will clear it)
		toggle_pin(LED_PIN, LED_GPIO_PORT);
	}
}
extern void TIM2_IRQHandler(void) {
	TIM2->SR &= ~TIM_SR_UIF;
	toggle_pin(LED_PIN, LED_GPIO_PORT);
}

int main(void) {
	// initialize GPIO peripheral clock (on enabled ports)
	GPIO_port_init(BTN_GPIO_PORT);
	GPIO_port_init(LED_GPIO_PORT);
	EXTI_init();  // initialize EXTI
	enable_EXTI(BTN_PIN, BTN_GPIO_PORT, 1, 0);

	pin_init(LED_PIN, LED_GPIO_PORT, GPIO_output, GPIO_medium_speed, GPIO_no_pull);
	pin_init(BTN_PIN, BTN_GPIO_PORT, GPIO_input, GPIO_medium_speed, GPIO_pull_up);
	NVIC_EnableIRQ(EXTI15_10_IRQn);

	// TODO: configure the system clock to determine the peripheral clock speed
	TIM_init(TIM2, 8000, 1000, 1);
	NVIC_EnableIRQ(TIM2_IRQn);
	TIM_start(TIM2);

	// suspend cpu until an interrupt occurs
	while (1) { __WFI(); }
}