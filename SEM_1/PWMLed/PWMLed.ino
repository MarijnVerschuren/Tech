#define ANALOG_GND  A0
#define ANALOG      A1
#define ANALOG_HIGH A2
#define LED_GND     3
#define LED_B       4
#define LED_G       5
#define LED_R       2
#define SELECT_R    8
#define SELECT_G    9
#define SELECT_B    10


uint16_t raw;
uint8_t r, g, b;

void setup() {
  pinMode(ANALOG_GND,   OUTPUT);  digitalWrite(ANALOG_GND,  LOW);
  pinMode(ANALOG_HIGH,  OUTPUT);  digitalWrite(ANALOG_HIGH, HIGH);
  pinMode(LED_GND,      OUTPUT);  digitalWrite(LED_GND,     LOW);
  pinMode(LED_B,        OUTPUT);
  pinMode(LED_G,        OUTPUT);
  pinMode(LED_R,        OUTPUT);
  pinMode(SELECT_R,     INPUT);
  pinMode(SELECT_G,     INPUT);
  pinMode(SELECT_B,     INPUT);
}

void loop() {
  raw = analogRead(ANALOG);
  if (digitalRead(SELECT_R)) { r = map(raw, 0, 1023, 0, 255); }
  if (digitalRead(SELECT_G)) { g = map(raw, 0, 1023, 0, 255); }
  if (digitalRead(SELECT_B)) { b = map(raw, 0, 1023, 0, 255); }
  analogWrite(LED_R, r);
  analogWrite(LED_G, g);
  analogWrite(LED_B, b);
}
