#define r_led DDG5  // pin 4 (G5)
#define g_led DDE3  // pin 5 (E3)
#define b_led DDH3  // pin 6 (H3)
#define y_led DDH4  // pin 7 (H4)
#define builtin_led DDB7  // pin 13 (B7) 

#define delay_ms 200



void setup() {
  // https://www.electronicshub.org/wp-content/uploads/2021/01/Arduino-Mega-Pinout.jpg
  // set leds as output
  DDRB |= (1 << builtin_led);           // builtin
  DDRE |= (1 << g_led);                 // g_led
  DDRG |= (1 << r_led);                 // r_led
  DDRH |= (1 << b_led) | (1 << y_led);  // b_led, y_led
  PORTH ^= (1 << b_led) | (1 << y_led);  // toggle the blue and yellow led so that they are out of sync with the red and green led
  Serial.begin(9600);
  Serial.print(float(1000 / delay_ms), 2);
  Serial.println(" Events per second");


  /*  // pwm
  ICR1 = 0xffff  // timer rollover

  OC0B = (0xffff >> 2)  // 1/2 duty cycle
  OC3A = (0xffff >> 3)  // 1/4 duty cycle
  OC4A = (0xffff >> 4)  // 1/8 duty cycle
  OC4B = (0xffff >> 5)  // 1/16 duty cycle
  
  TCCR0A |= (1 << COM0B1);
  TCCR3A |= (1 << COM3A1);
  TCCR4A |= (1 << COM4B1) | (1 << COM4A1);
  */
}

void loop() {
  // toggle leds
  PORTB ^= (1 << builtin_led);           // builtin
  PORTE ^= (1 << g_led);                 // g_led
  PORTG ^= (1 << r_led);                 // r_led
  PORTH ^= (1 << b_led) | (1 << y_led);  // b_led, y_led
  
  Serial.println((1 << builtin_led) & PORTB ? "LED ON": "LED OFF");
  delay(delay_ms);
}
