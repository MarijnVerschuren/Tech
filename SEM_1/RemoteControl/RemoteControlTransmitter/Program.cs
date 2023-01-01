using System;
using System.Collections.Generic;
using System.IO.Ports;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace RemoteControlTransmitter {
	internal class Program {
		static void Main(string[] args) {
			SerialPort ser = new SerialPort();

			Console.Write("port name: ");	ser.PortName = Console.ReadLine();
			Console.Write("baud: ");		ser.BaudRate = Convert.ToInt32(Console.ReadLine());  // int???? (so it can be negative baud....)
			ser.ReadTimeout =	500;
			ser.WriteTimeout =	500;

			ser.Open();

			// since C# is cant really work with structs, pointers and other fundemental paradigms im am using an array in this case...
			byte[] msg = new byte[4];

			while (ser.BytesToRead < 4) {}
			ser.Read(msg, 0, 4);

			byte max_id = msg[0];  // id field in struct

			while (true) {
				Console.Write("id (0 - " + max_id.ToString() + "): "); msg[0] = Convert.ToByte(Console.ReadLine());
				Console.Write("R: "); msg[1] = Convert.ToByte(Console.ReadLine());
				Console.Write("G: "); msg[2] = Convert.ToByte(Console.ReadLine());
				Console.Write("B: "); msg[3] = Convert.ToByte(Console.ReadLine());
				ser.Write(msg, 0, 4);
			}
		}
	}
}
