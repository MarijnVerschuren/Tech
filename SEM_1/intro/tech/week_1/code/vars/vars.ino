#include "macro.hpp"

// integers
int8    signed_byte                     = int8min;
uint8   unsigned_byte                   = uint8max;
int16   signed_word                     = int16min;
uint16  unsigned_word                   = uint16max;
int32   signed_doubleword               = int32min;
uint32  counter                         = 0;
int64   signed_quadword                 = int64min;
uint64  unsigned_quadword               = uint64max;
// reals
f32     floating_poin                   = f32min;
f64     double_precision_floating_point = f64max;


void setup() {
  Serial.begin(9600);
  f32 flt = 0.3;
  uint32 flt_int = *((uint32*)&flt);
  Serial.print(flt, 1);
  Serial.print(" -> ");
  Serial.println(flt_int, BIN);
  Serial.print("\n8 bit signed int min: "); Serial.println(signed_byte, DEC);
  Serial.print("8 bit signed int max: "); Serial.println(int8max, DEC);
  Serial.print("8 bit unsigned int max: "); Serial.println(unsigned_byte, DEC);
  Serial.print("16 bit signed int min: "); Serial.println(signed_word, DEC);
  Serial.print("16 bit signed int max: "); Serial.println(int16max, DEC);
  Serial.print("16 bit unsigned int max: "); Serial.println(unsigned_word, DEC);
  Serial.print("32 bit signed int min: "); Serial.println(signed_doubleword, DEC);
  Serial.print("32 bit signed int max: "); Serial.println(int32max, DEC);
  Serial.print("32 bit unsigned int max: "); Serial.println(uint32max, DEC);
  //Serial.print("64 bit signed int min: "); Serial.println(signed_quadword, DEC);
  //Serial.print("64 bit signed int max: "); Serial.println(int64max, DEC);
  //Serial.print("64 bit unsigned int max: "); Serial.println(unsigned_quadword, DEC);
  Serial.print("\n32 bit float max: "); Serial.println(f32max, 9);
  Serial.print("32 bit float min: "); Serial.println(floating_poin, 9);
  Serial.print("64 bit float max: "); Serial.println(double_precision_floating_point, 15);
  Serial.print("64 bit float min: "); Serial.println(f64min, 15);
}

void loop() {
  counter++;
  delay(1000);
  Serial.println(counter);
}
