using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading;
using System.Threading.Tasks;


namespace TraficControlCS {
	internal class Program {
		// static readonly is the only thing close to a static const...
		static readonly int MF_BYCOMMAND =	0x00000000;
		static readonly UInt16 SC_MINIMIZE =	0xF020;
		static readonly UInt16 SC_MAXIMIZE =	0xF030;
		static readonly UInt16 SC_SIZE =		0xF000;

		[DllImport("user32.dll")]
		public static extern int DeleteMenu(IntPtr hMenu, int nPosition, int wFlags);

		[DllImport("user32.dll")]
		private static extern IntPtr GetSystemMenu(IntPtr hWnd, bool bRevert);

		[DllImport("kernel32.dll", ExactSpelling = true)]
		private static extern IntPtr GetConsoleWindow();


		static int Main(string[] args) {
			IntPtr handle = GetConsoleWindow();
			if (handle == IntPtr.Zero) { return -1; }  // error no console handle
			IntPtr sysMenu =	GetSystemMenu(handle, false);
			// disable resizing, maximizing and minimizing
			DeleteMenu(sysMenu, SC_MINIMIZE,	MF_BYCOMMAND);
			DeleteMenu(sysMenu, SC_MAXIMIZE,	MF_BYCOMMAND);
			DeleteMenu(sysMenu, SC_SIZE,		MF_BYCOMMAND);
			// set window size
			Console.BufferWidth =   Console.WindowWidth =   32;
			Console.BufferHeight =  Console.WindowHeight =  16;
			Console.CursorVisible = false;  // hide cursor

			Trafic_Light a = new Trafic_Light();
			Trafic_Light b = new Trafic_Light();
			UInt32 last_transition = 0;

			Console.WriteLine("   Press '<-' or '->' to switch");
			Console.WriteLine("   manually or wait 10 seconds");
			while (true) {  // draw loop
				// variable initialization
				// made var for now (decreasing precision) because c# is just unwieldy...
				UInt32 now = (UInt32)DateTimeOffset.Now.ToUnixTimeMilliseconds();
				Trafic_State state_a = a.get_state();
				Trafic_State state_b = b.get_state();

				// input handleing 
				if (Console.KeyAvailable && state_a == a.get_transition_state() && state_b == b.get_transition_state()) {
					switch (Console.ReadKey(true).Key) {
						case ConsoleKey.LeftArrow:
							a.start_state_transition(Trafic_State.GREEN);
							b.start_state_transition(Trafic_State.RED);
							last_transition = now; break;
						case ConsoleKey.RightArrow:
							a.start_state_transition(Trafic_State.RED);
							b.start_state_transition(Trafic_State.GREEN);
							last_transition = now; break;
					}  //  else clear inputs so none stack up during transition
				} else { while (Console.KeyAvailable) { Console.ReadKey(false); } }

				// updating and drawing
				a.update();	a.draw(8,	3);
				b.update();	b.draw(22,	3);

				// auto toggle timer
				if (now - last_transition > 10000) {
					last_transition = now;
					if (state_a == state_b) { continue; }  // filter valid states
					if ((state_a == Trafic_State.GREEN || state_a == Trafic_State.RED) && (state_b == Trafic_State.GREEN || state_b == Trafic_State.RED)) {
						a.start_state_transition(state_b);
						b.start_state_transition(state_a);
					}
				}
			}
		}
	}
}