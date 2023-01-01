#define LED_GND_PIN 3
#define LED_A_PIN 2  // E4
#define LED_B_PIN 4  // G5

// frequency in Hz
#define LED_A_FREQ 2
#define LED_B_FREQ 5
uint32_t last_led_a_pulse = 0;
uint32_t last_led_b_pulse = 0;

void update_led_a();
void update_led_b();


void setup() {
  pinMode(LED_GND_PIN, OUTPUT);
  pinMode(LED_A_PIN, OUTPUT);
  pinMode(LED_B_PIN, OUTPUT);

  digitalWrite(LED_GND_PIN, LOW);
}

void loop() {
  update_led_a();
  update_led_b();
}

void update_led_a() {
  if (millis() - last_led_a_pulse > (1000 / LED_A_FREQ)) {
    last_led_a_pulse = millis();
    PORTE ^= (1 << 4);
  }
}

void update_led_b() {
  if (millis() - last_led_b_pulse > (1000 / LED_B_FREQ)) {
    last_led_b_pulse = millis();
    PORTG ^= (1 << 5);
  }
}