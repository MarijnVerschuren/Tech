#include <Arduino.h>
#include <Wire.h>

// the library source is placed here because it was not compiled in the lib directory
#include "SFE_MicroOLED.h"


#define RESET_PIN A0

#ifdef MSM
#define OWN_ADDR 0x50
#define PEER_ADDR 0x51
uint8_t I2C_master = 1;
#define OWN_GAME p1
#define PEER_GAME p2
#define SCREEN_POS 0
#else
#define OWN_ADDR 0x51
#define PEER_ADDR 0x50
uint8_t I2C_master = 0;
#define OWN_GAME p2
#define PEER_GAME p1
#define SCREEN_POS 32
#endif
#define MASTER_MODE_TIMEOUT 1000

void (*SWRST)(void) = NULL;	// declare software reset function
uint8_t* screen_buffer = NULL;
const uint32_t tetris_blocks[] = {
	// rotation 0 (CW)
	0x01010101,	// I-block
	0x00020203,	// J-block
	0x00030202,	// L-block
	0x00000303,	// O-block
	0x00010302,	// S-block
	0x00020302,	// T-block
	0x00020301,	// Z-block
	// rotation 1
	0x0000000f,	// I-block
	0x00000107,	// J-block
	0x00000407,	// L-block
	0x00000303,	// O-block
	0x00000603,	// S-block
	0x00000207,	// T-block
	0x00000306,	// Z-block
	// rotation 2
	0x00010101,	// I-block
	0x00030101,	// J-block
	0x00010103,	// L-block
	0x00000303,	// O-block
	0x00010302,	// S-block
	0x00010301,	// T-block
	0x00020301,	// Z-block
	// rotation 3
	0x0000000F,	// I-block
	0x00000704,	// J-block
	0x00000701,	// L-block
	0x00000303,	// O-block
	0x00000603,	// S-block
	0x00000702,	// T-block
	0x00000306,	// Z-block
};

class Tetris_Block {  // 2 bytes
	uint8_t block_id: 3; // 0 - 6	(3 bit)
	uint8_t x: 5;    // 0 - 31	(5 bit)
	uint8_t y: 6;    // 0 - 47	(6 bit)
	uint8_t rotation: 2;    // 0 - 3	(2 bit)


	inline uint32_t get_bitmap() { return tetris_blocks[this->rotation * 7 + this->block_id]; }

	inline uint8_t *get_screen_buffer_offset(uint8_t screen_offset) {
		uint8_t row = this->y / 8;
		return (uint8_t *) &screen_buffer[x + screen_offset + (row * 64)];
	}

	uint32_t transform_bitmap(uint32_t bitmap, int8_t offset) {
		if (offset > 0) {
			for (uint8_t i = 0; i < 4; i++) { ((uint8_t *) &bitmap)[i] <<= offset; }
			return bitmap;
		}
		for (uint8_t i = 0; i < 4; i++) { ((uint8_t *) &bitmap)[i] >>= (-offset); }
		return bitmap;
	}

	inline uint8_t collide() {
		uint8_t *ptr = get_screen_buffer_offset(SCREEN_POS);  // a little hacky but collisions are only on master
		uint32_t bitmap = get_bitmap();
		int8_t offset = this->y % 8;
		uint8_t height = get_height(bitmap);
		if (this->y + height > 47) { return true; }  // at the bottom
		return (  // check if any pixel is already set in the screen buffer
				(*((uint32_t *) ptr) & transform_bitmap(bitmap, offset)) ||
				(
						((offset + height) > 8) &&  // check split part
						(*((uint32_t *) (ptr + 64)) & transform_bitmap(bitmap, offset - 8))
				)
		);
	}

public:
	inline uint8_t get_height(uint32_t bitmap) {
		if (bitmap & 0x08080808) { return 4; }
		if (bitmap & 0x04040404) { return 3; }
		if (bitmap & 0x02020202) { return 2; }
		if (bitmap & 0x01010101) { return 1; }
		return 0;
	}

	void draw(uint8_t screen_offset) {
		uint8_t *ptr = get_screen_buffer_offset(screen_offset);
		uint32_t bitmap = get_bitmap();
		int8_t offset = this->y % 8;

		*((uint32_t *) ptr) |= transform_bitmap(bitmap, offset);
		if ((offset + get_height(bitmap)) > 8) {  // bitmap is split along rows
			*((uint32_t *) (ptr + 64)) |= transform_bitmap(bitmap, offset - 8);
		}
	}

	inline uint8_t set(uint8_t block_id, uint8_t x, uint8_t y, uint8_t rotation) {
		this->block_id = block_id;
		this->x = x;
		this->y = y;
		this->rotation = rotation;
		return collide();  // return true if collided
	}

	inline uint8_t move_down() {
		this->y++;
		if (collide()) { this->y--; return true; }  // revert change on collision
		return false;
	}
	inline uint8_t move_right() {
		this->x++;
		if (collide()) { this->x--; return true; }  // revert change on collision
		return false;
	}
	inline uint8_t move_left() {
		this->x--;
		if (collide()) { this->x++; return true; }  // revert change on collision
		return false;
	}
	inline uint8_t rotate() {
		this->rotation++;
		if (collide()) { this->rotation--; return true; }  // revert change on collision
		return false;
	}
};

class Tetris {
public:
	Tetris_Block blocks[20];	// theoretical max block count (384)
	uint32_t last_step = 0;
	uint32_t step_delay = 1000;
	uint16_t block_count = 0;
	uint16_t cursor = 0;			// currently active block (equal to count if none)

	void update() {  // image has to be drawn first!
		// update active block
		if (this->cursor != this->block_count) { user_input(); }
		else { new_block(); }
	}
	void draw(uint8_t screen_offset) {
		for (uint16_t i = 0; i < this->cursor; i++) { this->blocks[i].draw(screen_offset); }  // draw all blocks except active
	}
	void draw_cursor(uint8_t screen_offset) { this->blocks[this->cursor].draw(screen_offset); }
	void user_input() {
		if (millis() - this->last_step > this->step_delay) {
			this->last_step = millis();
			if (this->blocks[this->cursor].move_down()) { this->cursor = this->block_count; }  // disable block
		}
		// TODO joystick input
	}
	void new_block() {
		if (this->blocks[this->block_count].set(random(7), random(28), 0, random(4))) { SWRST(); }  // game over
		this->cursor = this->block_count; this->block_count++;
	}

	void reset() { this->block_count = 0; this->cursor = 0; }
};


MicroOLED oled;
uint32_t latest_master_mode = 0;
Tetris p1;
Tetris p2;
uint8_t new_game = false;

struct {
	Tetris_Block block;
	uint16_t index		: 15;  // 384 is max
	uint8_t new_game	: 1;
} packet;


void I2C_callback(int size) {  // function called when data is received
	if (size < sizeof(packet)) { return; }
	Wire.readBytes((uint8_t*)&packet, sizeof(packet));
	if (packet.index > PEER_GAME.cursor) {
		PEER_GAME.block_count++;
		PEER_GAME.cursor = packet.index;
	} PEER_GAME.blocks[packet.index] = packet.block;
	if (packet.new_game) { p1.reset(); p2.reset(); }
	I2C_master = 1;
}

void I2C_send_state() {  // hand token out to peer
	packet.index = OWN_GAME.cursor;
	packet.block = OWN_GAME.blocks[packet.index];
	packet.new_game = new_game;
	if (new_game) { new_game = false; }
	Wire.beginTransmission(PEER_ADDR);
	Wire.write((uint8_t*)&packet, sizeof(packet));
	Wire.endTransmission();
	I2C_master = 0;
}


void setup() {
	pinMode(LED_BUILTIN, OUTPUT);
	digitalWrite(LED_BUILTIN, LOW);
	pinMode(RESET_PIN, INPUT_PULLUP);

	Serial.begin(115200);
	Serial.print("started on ");
	Serial.println(OWN_ADDR, HEX);

	screen_buffer = new uint8_t[384]();
	if (!screen_buffer) { Serial.println("allocation error"); SWRST(); }
	OWN_GAME.new_block();
	new_game = true;

	Wire.begin(OWN_ADDR);  // start receiving as slave
	Wire.onReceive(I2C_callback);
	oled.begin(0x3D, Wire);
}

void loop() {
	if (!digitalRead(RESET_PIN)) { SWRST(); }  // custom reset so that resetting mcu does not interfere with OLED

	if (!I2C_master &&  (millis() - latest_master_mode) < MASTER_MODE_TIMEOUT) { return; }
	latest_master_mode = millis();
	digitalWrite(LED_BUILTIN, !digitalRead(LED_BUILTIN));

	oled.clear(CMD_CLEAR);
	memset(screen_buffer, 0x00, 384);  // reset screen buffer

	p1.draw(0);
	p2.draw(32);
	// updating game is done after drawing static blocks because the collisions are done by looking in the pixel buffer
	OWN_GAME.update();
	p1.draw_cursor(0);
	p2.draw_cursor(32);

	oled.drawBitmap(screen_buffer);
	oled.display();  // Draw to the screen

	I2C_send_state();
}
// TODO add joystick
// TODO: row deletion!!!!