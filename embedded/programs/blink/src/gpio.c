//
// Created by marijn on 2/13/23.
//
#include "gpio.h"


void GPIO_init(void) {
	RCC->AHBENR |= RCC_AHBENR_GPIOAEN;	// enable the peripheral clock for gpio port A
}

void set_pin_mode(uint8_t pin, GPIO_TypeDef* port, GPIO_MODE_TypeDef mode) {
	port->MODER |= (mode << (pin << 1));
}
void toggle_pin(uint8_t pin, GPIO_TypeDef* port) {
	port->ODR ^= (1 << pin);
}
void write_pin(uint8_t pin, GPIO_TypeDef* port, uint8_t data) {
	if (data)	{ port->ODR |= (1 << pin); }
	else		{ port->ODR &= ~(1 << pin); }
}
