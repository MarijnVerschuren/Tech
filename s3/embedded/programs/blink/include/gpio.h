//
// Created by marijn on 2/13/23.
//

#ifndef STM32F303RET6_GPIO_H
#define STM32F303RET6_GPIO_H
#include "main.h"

typedef enum {
	GPIO_input =	0b00,
	GPIO_output =	0b01,
	GPIO_alt_func =	0b10,
	GPIO_analog =	0b11
} GPIO_MODE_TypeDef;

#define LED_PIN 5
#define LED_GPIO_PORT GPIOA

void GPIO_init(void);
void set_pin_mode(uint8_t pin, GPIO_TypeDef* port, GPIO_MODE_TypeDef mode);
void toggle_pin(uint8_t pin, GPIO_TypeDef* port);

#endif //STM32F303RET6_GPIO_H
