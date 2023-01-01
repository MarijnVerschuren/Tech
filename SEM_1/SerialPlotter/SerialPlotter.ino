void setup() {
  Serial.begin(115200);
  pinMode(A0, OUTPUT);
  digitalWrite(A0, LOW);
  pinMode(A2, OUTPUT);
  digitalWrite(A2, HIGH);
}

void loop() { 
  uint16_t raw = analogRead(A1);
  Serial.print("\nraw:");       Serial.print(raw);
  Serial.print(",percentage:"); Serial.print((double)raw / 10.24);
}