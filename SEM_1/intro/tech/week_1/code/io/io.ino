#define button_0 DDH6  // pin 9 (H6)
#define button_1 DDB4  // pin 10 (B4)

// https://www.electronicshub.org/wp-content/uploads/2021/01/Arduino-Mega-Pinout.jpg



void setup() {
  // set button pins as input
  DDRH = DDRH & (~(1 << button_0));
  DDRB = DDRB & (~(1 << button_1));
  // pull the pins high
  PORTH |= (1 << button_0);
  PORTB |= (1 << button_1);
}

void loop() {
  // read
  PINH & (1 << button_0);
  PINB & (1 << button_1);
}
