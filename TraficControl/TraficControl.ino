#define RED_A_PIN 2
#define YELLOW_A_PIN 4
#define GREEN_A_PIN 6

#define RED_B_PIN 8
#define YELLOW_B_PIN 10
#define GREEN_B_PIN 12

#define SENSOR_A_PIN 14
#define SENSOR_B_PIN 15

#define TRAFIC_AUTO_TRANSITION_DELAY 10000
#define TRAFIC_TRANSITION_DELAY 3500  // on a 50km/h road
#define TRAFIC_PULSE_DELAY 1000
#define DEBOUNCE_DELAY 50  // ms

// function prototypes and typedefs
typedef void (*toggle_function_t)(uint8_t);
void set_trafic_light_a(uint8_t sensor_state);
void set_trafic_light_b(uint8_t sensor_state);

// classes and enums
class Button {
private:
  uint8_t           pin;
  uint8_t           debounce_delay;
  uint8_t           debounce_time;
  uint8_t           debounce_state;
  toggle_function_t func;
  
  uint8_t           state; 
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

  operator bool()     { return this->state; }
  uint8_t get_state() { return this->state; }
};

enum Trafic_State : uint8_t {
  GREEN =   0x0,
  YELLOW =  0x1,
  RED =     0x2,
  NONE =    0x3,  // blinking yellow
};

class Trafic_Light {
private:
  uint8_t   pins[3];
  
  uint32_t  transition_delay;
  uint32_t  transition_start;
  uint8_t   transition_state;
  uint32_t  pulse_delay;
  uint32_t  last_pulse = 0;

  uint8_t state;

public:
  Trafic_Light(uint8_t green_pin, uint8_t yellow_pin, uint8_t red_pin, uint32_t pulse_delay = TRAFIC_PULSE_DELAY, uint8_t inital_state = Trafic_State::NONE) {
    this->pins[0] = green_pin;    pinMode(green_pin, OUTPUT);
    this->pins[1] = yellow_pin;   pinMode(yellow_pin, OUTPUT);
    this->pins[2] = red_pin;      pinMode(red_pin, OUTPUT);
    this->pulse_delay = pulse_delay;
    this->transition_state = inital_state;  // disable transitioning
    set_state(inital_state);
  }

  void set_state(uint8_t state) {
    this->state = state;
    if (state == Trafic_State::NONE) { state = Trafic_State::YELLOW; }  // set to yellow on none state
    for (uint8_t i = 0; i < 3; i++) {
      if (i == state) { digitalWrite(this->pins[i], HIGH); continue; }
      digitalWrite(this->pins[i], LOW);
    }
  }

  void start_state_transition(uint8_t to_state, uint32_t transition_delay = TRAFIC_TRANSITION_DELAY) {
    if (to_state == this->state) { return; }
    if (this->state == Trafic_State::GREEN && to_state == Trafic_State::RED) { set_state(Trafic_State::YELLOW); }
    this->transition_delay = this->state == Trafic_State::NONE ? 0 : transition_delay;  // omit delay when changing from NONE state
    this->transition_state = to_state;
    this->transition_start = millis();
  }

  void update() {
    if (millis() - this->last_pulse > this->pulse_delay && this->state == Trafic_State::NONE) {
      this->last_pulse = millis();
      uint8_t pin = this->pins[Trafic_State::YELLOW];
      digitalWrite(pin, !digitalRead(pin));
    }
    if (this->transition_state != this->state && millis() - this-> transition_start > this->transition_delay) {
      set_state(this->transition_state);
    }
  }
  
  uint8_t get_state()             { return this->state; }
  uint8_t get_transition_delay()  { return this->transition_delay; }
};

// initialze buttons and trafic lights
Button sensor_a(SENSOR_A_PIN, DEBOUNCE_DELAY, &set_trafic_light_a);
Button sensor_b(SENSOR_B_PIN, DEBOUNCE_DELAY, &set_trafic_light_b);
Trafic_Light trafic_light_a(GREEN_A_PIN, YELLOW_A_PIN, RED_A_PIN);
Trafic_Light trafic_light_b(GREEN_B_PIN, YELLOW_B_PIN, RED_B_PIN);
uint32_t last_transition;

void setup() {
  for (uint8_t i = 2; i < 14; i++) {  if (i % 2 == 1) { pinMode(i, OUTPUT); digitalWrite(i, LOW); } }  // set all GND pins
  last_transition = millis();
}

void loop() {
  trafic_light_a.update();
  trafic_light_b.update();
  sensor_a.check();
  sensor_b.check();

  // auto toggleing trafic lights
  if (millis() - last_transition > TRAFIC_AUTO_TRANSITION_DELAY) {
    uint8_t state_a = trafic_light_a.get_state();
    uint8_t state_b = trafic_light_b.get_state();
    if (state_a == state_b) { return; }  // filter valid states
    if ((state_a == Trafic_State::GREEN || state_a == Trafic_State::RED) && \
        (state_b == Trafic_State::GREEN || state_b == Trafic_State::RED)) {
      trafic_light_a.start_state_transition(state_b);
      trafic_light_b.start_state_transition(state_a);
      last_transition = millis() + max(trafic_light_a.get_transition_delay(), trafic_light_b.get_transition_delay());
    }
  }
}

// these functions will make sure that the transitions is only set into actions once even if a car activates on the sensor for an extended period of time
void set_trafic_light_a(uint8_t sensor_state) {
  if (!sensor_state) { return; }
  last_transition = millis();
  trafic_light_a.start_state_transition(Trafic_State::GREEN);
  trafic_light_b.start_state_transition(Trafic_State::RED);
}
void set_trafic_light_b(uint8_t sensor_state) {
  if (!sensor_state) { return; }
  last_transition = millis();
  trafic_light_a.start_state_transition(Trafic_State::RED);
  trafic_light_b.start_state_transition(Trafic_State::GREEN);
}