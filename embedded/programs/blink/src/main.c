#include "main.h"
#include "gpio.h"  // all pins are defined here
#define GPIOMODER (1 << (LED_BUILTIN << 1))



void ms_delay(int ms) {
   while (ms-- > 0) {
      volatile int x = 500;
      while (x-- > 0)
         __asm("nop");
   }
}

//Alternates blue and green LEDs quickly
int main(void) {
	GPIO_init();  // initialize GPIO peripheral clock (on enabled ports)

	set_pin_mode(LED_PIN, LED_GPIO_PORT, GPIO_output);

	while (1) {
		toggle_pin(LED_PIN, LED_GPIO_PORT);
		ms_delay(500);
	}
}