#include "main.h"
#include "gpio.h"	// all pins are defined here
#include "exti.h"
#include "tim.h"	// all timers and delays are defined here


volatile uint8_t state = 0;
extern void EXTI15_10_IRQHandler(void) {
	if(EXTI->PR & EXTI_PR_PR13) {
		EXTI->PR = EXTI_PR_PR13;  // clear interrupt pin (write to it will clear it)
		write_pin(LED_PIN, LED_GPIO_PORT, !read_pin(LED_PIN, LED_GPIO_PORT));
	}
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

	while (1) {
		//write_pin(LED_PIN, LED_GPIO_PORT, read_pin(BTN_PIN, BTN_GPIO_PORT));
	}
}


////// TODO: edit
void sys_clock_init(void) {
	uint32_t HSI_startup_counter = 0;

	// Enable HSI oscillator
	RCC->CR |= RCC_CR_HSION;

	// Wait until HSI is ready or timeout occurs
	while((RCC->CR & RCC_CR_HSIRDY) == 0)
	{
		HSI_startup_counter++;
		if(HSI_startup_counter > HSI_TIMEOUT_VALUE)
		{
			// HSI oscillator failed to start, handle error
			break;
		}
	}

	// Set HCLK (AHB bus) prescaler to 1
	RCC->CFGR &= ~(RCC_CFGR_HPRE);

	// Set PCLK1 (APB1 bus) prescaler to 2 (max value)
	RCC->CFGR |= RCC_CFGR_PPRE1_DIV2;

	// Set PCLK2 (APB2 bus) prescaler to 1
	RCC->CFGR &= ~(RCC_CFGR_PPRE2);

	// Set PLL source to HSI, set PLL multiplier to 9 (x10)
	RCC->CFGR &= ~(RCC_CFGR_PLLSRC | RCC_CFGR_PLLMUL);
	RCC->CFGR |= RCC_CFGR_PLLSRC_HSI_PREDIV | RCC_CFGR_PLLMUL9;

	// Enable PLL
	RCC->CR |= RCC_CR_PLLON;

	// Wait until PLL is ready or timeout occurs
	while((RCC->CR & RCC_CR_PLLRDY) == 0)
	{
		HSI_startup_counter++;
		if(HSI_startup_counter > PLL_TIMEOUT_VALUE)
		{
			// PLL oscillator failed to start, handle error
			break;
		}
	}

	// Set SYSCLK (system clock) source to PLL
	RCC->CFGR &= ~(RCC_CFGR_SW);
	RCC->CFGR |= RCC_CFGR_SW_PLL;

	// Wait until SYSCLK is ready or timeout occurs
	while((RCC->CFGR & RCC_CFGR_SWS) != RCC_CFGR_SWS_PLL)
	{
		HSI_startup_counter++;
		if(HSI_startup_counter > SYSCLK_TIMEOUT_VALUE)
		{
			// SYSCLK failed to switch to PLL, handle error
			break;
		}
	}

	// Set flash latency according to new SYSCLK frequency (2 WS at 1.8V-2.1V, 3 WS at 2.1V-2.4V)
	if((FLASH->ACR & FLASH_ACR_LATENCY) != FLASH_ACR_LATENCY_2)
	{
		FLASH->ACR &= ~(FLASH_ACR_LATENCY);
		FLASH->ACR |= FLASH_ACR_LATENCY_2;
	}
}