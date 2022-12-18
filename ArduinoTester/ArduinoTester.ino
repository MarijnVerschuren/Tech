// Arduino pin testing code using the GPIO registers
// PIN regs are at 3n     (holds state)
// DDR regs are at 1+3n   (holds data dir) (set = output)
// PORT regs are at 2+3n  (set state)

void setup() {
  // serial to send failures back
  Serial.begin(9600);
}

// holds all excluded pins from registers a - g
const char port_names[7] = {'A', 'B', 'C', 'D', 'E', 'F', 'G'};
uint8_t exclude[7] = {
  0b00000000, // a
  0b00000000, // b
  0b00000000, // c
  0b00000000, // d
  0b11000000, // e  (TX and RX pins are used for Serial and flashing so these have to be working)
  0b00000000, // f
  0b11000000  // g  (RD and WR pins are used to signal a read or write instruction to an external memory chip and are pulled low if unused)
};

void loop() {
  uint8_t mask, state, error = 0;
  for (uint8_t i = 0; i < 7; i++) {
    mask = 0xff ^ exclude[i];
    _SFR_IO8(3 * i + 1)     = mask;    // set all included pins as output
    _SFR_IO8(3 * i + 2)     = mask;    // set all included pins high
    _SFR_IO8(3 * i + 1)     = ~mask;   // set all included pins as input
    state = _SFR_IO8(3 * i) & mask;    // check all included pin states
    if (state != mask) {
      Serial.print("ERROR IN PORT_");
      Serial.print(port_names[i]);
      Serial.print(" AT PIN: ");
      Serial.print(state ^ mask, BIN);
      Serial.print("\n");
      error = 1;
    }
  }
  if (!error) { Serial.print("NO ERRORS DETECTED!\n"); }
  while (1) {}  // end program
}