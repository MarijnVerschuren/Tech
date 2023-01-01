constexpr uint8_t led_count = 1;
constexpr uint8_t pins[1][4] = {
  {3, 2, 4, 5}  // gnd, r, g, b (of led 1)
};

struct {
  uint8_t id;
  uint8_t r;
  uint8_t g;
  uint8_t b;
} input;


void setup() {
  for (uint8_t i = 0; i < led_count + 1; i++) {
    pinMode(pins[i][0], OUTPUT);
    digitalWrite(pins[i][0], LOW);
    pinMode(pins[i][1], OUTPUT);
    pinMode(pins[i][2], OUTPUT);
    pinMode(pins[i][3], OUTPUT);
  }

  Serial.begin(115200);

  while (Serial.available() < 4) {
    input.id = led_count - 1;  // max id
    Serial.write((char*)&input, 4);
    delay(200);  // send "handshake" 5x per second
  }
}

void loop() {
  if (Serial.available() > 3) { Serial.readBytes((char*)&input, 4); }
  if (!(input.id < led_count)) { return; }
  analogWrite(pins[input.id][1], input.r);
  analogWrite(pins[input.id][2], input.g);
  analogWrite(pins[input.id][3], input.b);
}