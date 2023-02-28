//
// Created by marijn on 2/13/23.
//
#include "gpio.h"


/*!< misc */
uint8_t port_to_int(GPIO_TypeDef* port) {
	return ((uint32_t)(port - AHB2PERIPH_BASE) >> 10u) & 0xfu;
}
/*!< init / disable */
void GPIO_port_init(GPIO_TypeDef* port) {
	if (port == GPIOA) { RCC->AHBENR |= RCC_AHBENR_GPIOAEN; return; }
	if (port == GPIOB) { RCC->AHBENR |= RCC_AHBENR_GPIOBEN; return; }
	if (port == GPIOC) { RCC->AHBENR |= RCC_AHBENR_GPIOCEN; return; }
	if (port == GPIOD) { RCC->AHBENR |= RCC_AHBENR_GPIODEN; return; }
	if (port == GPIOE) { RCC->AHBENR |= RCC_AHBENR_GPIOEEN; return; }
	if (port == GPIOF) { RCC->AHBENR |= RCC_AHBENR_GPIOFEN; return; }
	if (port == GPIOG) { RCC->AHBENR |= RCC_AHBENR_GPIOGEN; return; }
	if (port == GPIOH) { RCC->AHBENR |= RCC_AHBENR_GPIOHEN; return; }
}
void GPIO_port_disable(GPIO_TypeDef* port) {
	if (port == GPIOA) { RCC->AHBENR &= ~RCC_AHBENR_GPIOAEN; return; }
	if (port == GPIOB) { RCC->AHBENR &= ~RCC_AHBENR_GPIOBEN; return; }
	if (port == GPIOC) { RCC->AHBENR &= ~RCC_AHBENR_GPIOCEN; return; }
	if (port == GPIOD) { RCC->AHBENR &= ~RCC_AHBENR_GPIODEN; return; }
	if (port == GPIOE) { RCC->AHBENR &= ~RCC_AHBENR_GPIOEEN; return; }
	if (port == GPIOF) { RCC->AHBENR &= ~RCC_AHBENR_GPIOFEN; return; }
	if (port == GPIOG) { RCC->AHBENR &= ~RCC_AHBENR_GPIOGEN; return; }
	if (port == GPIOH) { RCC->AHBENR &= ~RCC_AHBENR_GPIOHEN; return; }
}
void lock_pin_config(uint8_t pin, GPIO_TypeDef* port) {
	port->OTYPER &= ~(1 << pin);
}
void unlock_pin_config(uint8_t pin, GPIO_TypeDef* port) {
	port->OTYPER |= 1 << pin;
}
void set_pin_mode(uint8_t pin, GPIO_TypeDef* port, GPIO_MODE_TypeDef mode) {
	port->MODER |= (mode << (pin << 1u));
}
void set_pin_config(uint8_t pin, GPIO_TypeDef* port, GPIO_SPEED_TypeDef speed, GPIO_PULL_TypeDef pull) {
	port->OSPEEDR |= (speed << (pin << 1u));
	port->PUPDR |= (pull << (pin << 1u));
}
void pin_init(uint8_t pin, GPIO_TypeDef* port, GPIO_MODE_TypeDef mode, GPIO_SPEED_TypeDef speed, GPIO_PULL_TypeDef pull) {
	port->MODER |= (mode << (pin << 1u));
	port->OSPEEDR |= (speed << (pin << 1u));
	port->PUPDR |= (pull << (pin << 1u));
}
/*!< output */
void write_pin(uint8_t pin, GPIO_TypeDef* port, uint8_t data) {
	if (data)	{ port->ODR |= (1u << pin); }
	else		{ port->ODR &= ~(1u << pin); }
}
void toggle_pin(uint8_t pin, GPIO_TypeDef* port) {
	port->ODR ^= (1u << pin);
}
/*!< input */
uint8_t read_pin(uint8_t pin, GPIO_TypeDef* port) {
	return (port->IDR >> pin) & 1u;
}