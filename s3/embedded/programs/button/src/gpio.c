//
// Created by marijn on 2/13/23.
//
#include "gpio.h"


// init
void GPIO_init(void) {
	RCC->AHBENR |= RCC_AHBENR_GPIOAEN;  // enable the peripheral clock for gpio port A
	RCC->AHBENR |= RCC_AHBENR_GPIOCEN;  // enable the peripheral clock for gpio port C
}
void set_pin_mode(uint8_t pin, GPIO_TypeDef* port, GPIO_MODE_TypeDef mode) {
	port->MODER |= (mode << (pin << 1));
}
void set_pin_config(uint8_t pin, GPIO_TypeDef* port, GPIO_SPEED_TypeDef speed, GPIO_PULL_TypeDef pull) {
	port->OSPEEDR |= (speed << (pin << 1));
	port->PUPDR |= (pull << (pin << 1));
}
void pin_init(uint8_t pin, GPIO_TypeDef* port, GPIO_MODE_TypeDef mode, GPIO_SPEED_TypeDef speed, GPIO_PULL_TypeDef pull) {
	port->MODER |= (mode << (pin << 1));
	port->OSPEEDR |= (speed << (pin << 1));
	port->PUPDR |= (pull << (pin << 1));
}
// output
void write_pin(uint8_t pin, GPIO_TypeDef* port, uint8_t data) {
	if (data)	{ port->ODR |= (1 << pin); }
	else		{ port->ODR &= ~(1 << pin); }
}
void toggle_pin(uint8_t pin, GPIO_TypeDef* port) {
	port->ODR ^= (1 << pin);
}
// input
uint8_t read_pin(uint8_t pin, GPIO_TypeDef* port) {
	return (port->IDR >> pin) & 1;
}