using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace BankingAppCS {
	internal class Account {
		public String iban {
			get;
			private set;
		}
		public Double balance {
			get;
			private set;
		}
		public Account(String iban, Double balance) {
			this.iban = iban;
			this.balance = balance;
		}

		static public Account operator +(Account self, Double ammount) { self.balance = Math.Round(self.balance + ammount, 6); return self; }
		static public Account operator -(Account self, Double ammount) { self.balance = Math.Round(self.balance - ammount, 6); return self; }
	}

	internal class Banking {
		private List<Account> accounts = new List<Account>();
		private Random rd = new Random();

		private long LongRandom(long min, long max) {
			long result = rd.Next((Int32)(min >> 32), (Int32)(max >> 32));
			result = (result << 32);
			result = result | (long)rd.Next((Int32)min, (Int32)max);
			return result;
		}


		private String generate_iban() {
			String number, iban;
			do {
				number = LongRandom(0, 9999999999).ToString();
				iban = "NL29RABO" + ('0' * (10 - number.Length)) + number;
			} while (get_account(iban) != null);
			return iban;
		}


		public Account get_account(String iban) {  // this is the slow method 
			foreach (Account acc in accounts) {
				if (acc.iban == iban) { return acc; }
			} return null;
		}

		public String add_account() {
			String iban = generate_iban();
			accounts.Add(new Account(iban, 0));
			return iban;
		}

		public bool deposit(String dst, Double ammount) {
			Account dst_acc = get_account(dst);
			if (dst_acc == null) { return false; }
			dst_acc += ammount; return true;
		}

		public bool take_out(String src, Double ammount) {
			Account src_acc = get_account(src);
			if (src_acc == null) { return false; }
			src_acc -= ammount; return true;
		}

		public bool transfer(String src, String dst, Double ammount) {
			Account src_acc = get_account(src);
			Account dst_acc = get_account(dst);
			if (src_acc == null || dst_acc == null) { return false; }
			src_acc -= ammount; dst_acc += ammount; return true;
		}
	}
}
