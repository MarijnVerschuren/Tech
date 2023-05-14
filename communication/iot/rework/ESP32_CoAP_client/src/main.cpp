#include <Arduino.h>
#include <coap-simple.h>
#include <WiFi.h>


void callback_response(CoapPacket &packet, IPAddress ip, int port);
//145.93.85.248
//145.93.44.229
//127.0.0.1
IPAddress ip(145,93,44,169);
int port =5683;

const char* ssid = "MichieldeRouter";
const char* password = "Test12345";

WiFiUDP Udp;
Coap coap(Udp);

void callback_response(CoapPacket &packet, IPAddress ip, int port) {
  Serial.println("[Coap Response got]");

  char p[packet.payloadlen + 1];
  memcpy(p, packet.payload, packet.payloadlen);
  p[packet.payloadlen] = NULL;

  Serial.println(p);
}

void setup() {
    Serial.begin(115200);
    WiFi.begin(ssid, password);
    Serial.println("Connecting to wifi");
    while (WiFi.status() != WL_CONNECTED) {
    delay(500);
    yield();
    Serial.print(".");
    }
    Serial.println("");
    Serial.println("WiFi connected");
     // Print the IP address of client
     Serial.println(WiFi.localIP());

    coap.response(callback_response);

    coap.start();


}
void loop() {

    Serial.println("Send Request");
    int msgid = coap.get(ip,port, "time");
    delay(1000);
    coap.loop();
}
