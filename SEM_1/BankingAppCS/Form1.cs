using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Windows.Forms;


namespace BankingAppCS {
	public partial class Form1 : Form {
		Banking bank = new Banking();
		String[] ibans = { "", "" };

		public Form1() {
			InitializeComponent();
		}

		private void Form1_Load(object sender, EventArgs e) {
			ibans[0] = bank.add_account();
			ibans[1] = bank.add_account();
			label2.Text = ibans[0].ToString();  // account a
			label4.Text = ibans[1].ToString();  // account b
			update();
		}

		private void label1_Click(object sender, EventArgs e) { return; }
		private void label2_Click(object sender, EventArgs e) { return; }
		private void label3_Click(object sender, EventArgs e) { return; }
		private void label4_Click(object sender, EventArgs e) { return; }
		private void label5_Click(object sender, EventArgs e) { return; }
		private void label6_Click(object sender, EventArgs e) { return; }
		private void label7_Click(object sender, EventArgs e) { return; }

		private void textBox_TextChanged(object sender, EventArgs e) { label5.Text = ""; }

		private Double get_ammount() {
			Double ammount;
			try { ammount = Convert.ToDouble(textBox1.Text.Replace('.', ',')); }
			catch {
				label5.Text = "Input a valid number.";
				return Double.NaN;
			} if (ammount < 0) {
				label5.Text = "Input a positive number.";
				return Double.NaN;
			} return ammount;
		} 

		private void update() {
			label6.Text = bank.get_account(ibans[0]).balance.ToString();
			label7.Text = bank.get_account(ibans[1]).balance.ToString();
		}

		private void button1_Click(object sender, EventArgs e) {
			Double ammount = get_ammount();
			if (Double.IsNaN(ammount)) { return; }
			bank.deposit(ibans[0], ammount);
			update();
		}

		private void button2_Click(object sender, EventArgs e) {
			Double ammount = get_ammount();
			if (Double.IsNaN(ammount)) { return; }
			bank.take_out(ibans[0], ammount);
			update();
		}
		
		private void button3_Click(object sender, EventArgs e) {
			Double ammount = get_ammount();
			if (Double.IsNaN(ammount)) { return; }
			bank.transfer(ibans[0], ibans[1], ammount);
			update();
		}

		private void button4_Click(object sender, EventArgs e) {
			Double ammount = get_ammount();
			if (Double.IsNaN(ammount)) { return; }
			bank.deposit(ibans[1], ammount);
			update();
		}

		private void button5_Click(object sender, EventArgs e) {
			Double ammount = get_ammount();
			if (Double.IsNaN(ammount)) { return; }
			bank.take_out(ibans[1], ammount);
			update();
		}

		private void button6_Click(object sender, EventArgs e) {
			Double ammount = get_ammount();
			if (Double.IsNaN(ammount)) { return; }
			bank.transfer(ibans[1], ibans[0], ammount);
			update();
		}
		
		private void contextMenuStrip1_Opening(object sender, CancelEventArgs e) {

		}
	}
}
