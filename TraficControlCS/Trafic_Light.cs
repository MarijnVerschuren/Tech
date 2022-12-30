using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;


namespace TraficControlCS {
	enum Trafic_State : UInt16 {
		RED =		0x0,
		YELLOW =	0x1,
		GREEN =		0x2,
		NONE =		0x3,  // blinking yellow
	}

	internal class Trafic_Light {
		//static readonly Encoding ENC = Encoding.GetEncoding(437);  // extended ascii charset
		static readonly Encoding ENC = Encoding.Unicode;

		static readonly char[][] TRAFIC_LIGHT_LAMP = {
			new char[] { ' ',       '\u2584',   '\u2584',   ' ' },
			new char[] { '\u2590',  '\u2588',   '\u2588',   '\u258C' },
			new char[] { ' ',       '\u2580',   '\u2580',   ' ' },
		};
		static readonly UInt16[] TRAFIC_LIGHT_COLOR = { 12, 14, 10, 8 };  // 8 = off

		private UInt32 transition_delay;
		private UInt32 transition_start;
		private UInt32 pulse_delay;
		private UInt32 last_pulse = 0;
		private Trafic_State transition_state;
		private Trafic_State state;
		private Trafic_State color;  // values represent colors too


		private void set_state(Trafic_State state) { this.state = this.color = state; }

		public Trafic_Light(UInt32 pulse_delay = 1000, Trafic_State inital_state = Trafic_State.NONE) {
			this.pulse_delay = pulse_delay;
			this.transition_state = inital_state;
			set_state(inital_state);
		}

		public void start_state_transition(Trafic_State to_state, UInt32 transition_delay = 3500) {
			if (to_state == this.state) { return; }
			if (this.state == Trafic_State.GREEN && to_state == Trafic_State.RED) { set_state(Trafic_State.YELLOW); }
			this.transition_delay = this.state == Trafic_State.NONE ? 0 : transition_delay;  // omit delay when changing from NONE state
			this.transition_state = to_state;
			this.transition_start = (UInt32)DateTimeOffset.Now.ToUnixTimeMilliseconds();
		}

		public void update() {
			UInt32 now = (UInt32)DateTimeOffset.Now.ToUnixTimeMilliseconds();
			if (now - this.last_pulse > this.pulse_delay && this.state == Trafic_State.NONE) {
				this.last_pulse = now;
				this.color = this.color == Trafic_State.NONE ? Trafic_State.YELLOW : Trafic_State.NONE;  // toggle on and off
			}
			if (this.transition_state != this.state && now - this.transition_start > this.transition_delay) {
				set_state(this.transition_state);
			}
		}

		public void draw(UInt16 xoffset, UInt16 yoffset) {
			for (UInt16 l = 0; l < 3; l++) {  // loop over all lamps
				if (l == (UInt16)this.color)	{ Console.ForegroundColor = (System.ConsoleColor)TRAFIC_LIGHT_COLOR[l]; }  // set colors
				else							{ Console.ForegroundColor = (System.ConsoleColor)TRAFIC_LIGHT_COLOR[3]; }  // turn off
				for (UInt16 y = 0; y < 3; y++) {
					Console.SetCursorPosition(xoffset, y + 4 * l + yoffset);
					for (UInt16 x = 0; x < 4; x++) {
						Console.Write(TRAFIC_LIGHT_LAMP[y][x].ToString(), ENC);
					}
				}
			}
		}
		
		public Trafic_State get_state()				{ return this.state; }
		public Trafic_State get_transition_state()	{ return this.transition_state; }
		public UInt32 get_transition_delay()		{ return this.transition_delay; }
	}
}