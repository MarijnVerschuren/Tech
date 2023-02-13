//
// Created by marijn on 2/13/23.
//
#include "nvic.h"


void NVIC_init(void) {
	RCC->APB2ENR |= RCC_APB2ENR_SYSCFGEN;
}

void enable_EXTI(uint8_t EXTI_line, GPIO_TypeDef* EXTI_port, uint8_t falling_edge, uint8_t rising_edge) {
	EXTI_line &= 0xfu;  // only allow values upto 15
	uint8_t pos = (EXTI_line & 0x3u);
	SYSCFG->EXTICR[EXTI_line >> 2u] &= ~(0xfu << pos);
	SYSCFG->EXTICR[EXTI_line >> 2u] |= (0xfu & port_to_int(EXTI_port)) << pos;
	// set triggers
	EXTI->FTSR |= ((falling_edge & 1u) << EXTI_line);
	EXTI->RTSR |= ((rising_edge & 1u) << EXTI_line);
	EXTI->IMR |= (1u << EXTI_line);  // unmask interrupt
}