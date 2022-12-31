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

			Console.WriteLine("port name: ");	ser.PortName = Console.ReadLine();
			Console.WriteLine("baud: ");		ser.BaudRate = Convert.ToInt32(Console.ReadLine());  // int???? (so it can be negative baud....)
			ser.ReadTimeout =	500;
			ser.WriteTimeout =	500;

			ser.Open();
		}
	}
}
