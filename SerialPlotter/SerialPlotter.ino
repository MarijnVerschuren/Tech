#define AS5600_DEG_CONV 8.7890625e-2	/* 360/4096 */
#define AS5600_RAD_CONV 1.5339808e-3	/* 2pi/4096 */

void setup() {
  Serial.begin(115200);
}

char msg_buffer[30];  // text (14 chars) + raw (4 chars) + deg (6 chars) + rad (6 chars)
void loop() { 
  uint16_t raw = analogRead(A0) << 2;  // analog read only provides 10 bits of precision...
  sprintf(msg_buffer, "raw:%4u,deg:%4.1f,rad:%4.4f", raw, raw * AS5600_DEG_CONV, raw * AS5600_RAD_CONV);
  Serial.print(msg_buffer);
}
