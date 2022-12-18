#define LED_A_PIN 2
#define LED_B_PIN 4
#define LED_LOW_PIN 3
#define BTN_A_PIN 8
#define BTN_B_PIN 12

#define DEBOUNCE_DELAY 50  // ms

// function prototypes and typedefs
typedef void (*toggle_function_t)(uint8_t);
void toggle_led_a(uint8_t button_state);
void toggle_led_b(uint8_t button_state);

// button class
class Button {
private:
  uint8_t pin;
  uint8_t debounce_delay;
  uint8_t debounce_time;
  uint8_t debounce_state;
  toggle_function_t func;
  
public:
  Button(uint8_t pin, uint8_t debounce_delay, toggle_function_t func = nullptr) {
    this->pin = pin; pinMode(pin, INPUT);
    this->debounce_delay = debounce_delay;
    this->debounce_state = LOW;
    this->debounce_time = LOW;
    this->func = func;
    this->state = LOW;
  }

  void check() {  // only set state high if two checks in a row are high
  uint8_t reading = digitalRead(this->pin);
    if (reading != this->debounce_state) { this->debounce_time = millis(); }  // skip if last button state is different then now
    if (millis() - this->debounce_time > this->debounce_delay) {
      this->debounce_time = millis();
      if (this->state != reading) {
        this->state = reading;  // set state and run attached funtion when changing value
        if (this->func) { this->func(this->state); }
      }
    }
    this->debounce_state = digitalRead(this->pin);
  }

  operator bool() { return this->state; }

  uint8_t state; 
};

// initialze buttons
Button btn_a(BTN_A_PIN, DEBOUNCE_DELAY, &toggle_led_a);
Button btn_b(BTN_B_PIN, DEBOUNCE_DELAY, &toggle_led_b);

// initialize pins
void setup() {
  pinMode(LED_A_PIN, OUTPUT);
  pinMode(LED_B_PIN, OUTPUT);
  pinMode(LED_LOW_PIN, OUTPUT);

  digitalWrite(LED_LOW_PIN, LOW);
}

// constatnly check buttons
void loop() {
  btn_a.check();
  btn_b.check();
}

// only trigger on rising edge
void toggle_led_a(uint8_t button_state) { if (!button_state) { return; } PORTE ^= (1 << 4); }
void toggle_led_b(uint8_t button_state) { if (!button_state) { return; } PORTG ^= (1 << 5); }