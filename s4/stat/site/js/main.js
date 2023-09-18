// create random cookie and use it to create randomized survey
const colors = [
	"#d53e4f",
	"#f46d43",
	"#fdae61",
	"#fee08b",
	"#e6f598",
	"#abdda4",
	"#66c2a5",
	"#3288bd"
]

const option_a = document.getElementById("option_a");
const option_b = document.getElementById("option_b");
const cookie_offset = " ".charCodeAt(0);

window.onload = function() {
	let a, b;  // color indexes for the optionss
	if (document.cookie.length === 0) {
		do {  // create two unique numbers in range (0, 7)
			a = Math.round(Math.random() * 0x7);
			b = Math.round(Math.random() * 0x7);
		} while (a === b);
		document.cookie = String.fromCharCode(a | (b << 3) + cookie_offset);
	} else {
		let cookie = document.cookie.charCodeAt(0) - cookie_offset;
		a = cookie & 0x7;
		b = (cookie >> 3) & 0x7;
	}

	option_a.style.background = colors[a];
	option_b.style.background = colors[b];
	option_a.onclick = choose_a;
	option_b.onclick = choose_b;
};

function choose_a() {
	window.console.log("A chosen!!\n");
	send_result(option_a.style.background);
}
function choose_b() {
	window.console.log("B chosen!!\n");
	send_result(option_b.style.background);
}
function send_result(result) {
	// TODO: send result to the database
	// TODO: remove choices and lock user out via cookies
	window.console.log(result);
}
