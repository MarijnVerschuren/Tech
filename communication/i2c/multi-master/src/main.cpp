#include <Arduino.h>
#include <Wire.h>

// the library source is placed here because it was not compiled in the lib directory
#include "SFE_MicroOLED.h"


typedef struct {
	uint32_t counter_a;
	uint32_t counter_b;
} state_t;


#ifdef MSM
#define OWN_ADDR 0x50
#define PEER_ADDR 0x51
volatile uint8_t I2C_master = 1;
#define OWN_STATE counter_a
#else
#define OWN_ADDR 0x51
#define PEER_ADDR 0x50
volatile uint8_t I2C_master = 0;
#define OWN_STATE counter_b
#endif
#define MASTER_MODE_TIMEOUT 500


MicroOLED oled;

uint32_t latest_master_mode = 0;
uint32_t counter = 0;
volatile state_t* state;


void I2C_callback(int size) {  // function called when data is received
	if (Wire.available() < sizeof(state_t)) { return; }
	Wire.readBytes((uint8_t*)state, sizeof(state_t));
	I2C_master = 1;
}

void I2C_send_state(uint8_t peer) {  // hand token out to peer
	I2C_master = 0;
	Wire.beginTransmission(peer);
	Wire.write((uint8_t*)state, sizeof(state_t));
	Wire.endTransmission();
}


void setup() {
	pinMode(LED_BUILTIN, OUTPUT);
	digitalWrite(LED_BUILTIN, LOW);

	Serial.begin(115200);

	state = (state_t*)malloc(sizeof(state_t));
	if (!state) { for(;;) { Serial.print("alloc error"); } }

	Wire.begin(OWN_ADDR);  // start receiving as slave
	Wire.onReceive(I2C_callback);
	oled.begin(0x3D, Wire);
}

void loop() {
	if (!I2C_master &&  (millis() - latest_master_mode) < MASTER_MODE_TIMEOUT) { return; }
	latest_master_mode = millis();

	digitalWrite(LED_BUILTIN, !digitalRead(LED_BUILTIN));

	counter++;
	state->OWN_STATE = counter;
	oled.clear(CMD_CLEAR);
	oled.setCursor(0, 16);
	oled.print(state->counter_a);
	oled.setCursor(0, 32);
	oled.print(state->counter_b);
	oled.display(); // Draw to the screen

	delay(50);
	I2C_send_state(PEER_ADDR);
	delay(50);  // TODO: remove
}