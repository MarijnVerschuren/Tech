/**
 * constants
 */
const rounds = 12;
const colors = [
	"#d53e4fff",
	"#f46d43",
	"#fdae61",
	"#fee08b",
	"#e6f598",
	"#abdda4",
	"#66c2a5",
	"#3288bd"
]


/**
 * helpers
 */
const timeout = (cb, interval) => () => new Promise(resolve => setTimeout(() => cb(resolve), interval))
String.prototype.replaceAt = function(index, replacement) {
	return this.substring(0, index) + replacement + this.substring(index + replacement.length);
}

/**
 * html objects
 */
const survey = document.getElementById("survey");
const question = document.getElementById("question");
const option_a = document.getElementById("option_a");
const option_b = document.getElementById("option_b");



/**
 * functions
 */
window.onload = function() {
	// variables
	let cookie = document.cookie;
	let a, b;  // color indexes
	let rnd = 0;

	// handle cookies
	if (cookie.length === 0) {
		// TODO: add call to start for id (64 bit)
		// TODO: split cookies into id and rounds
		for (let _ = 0; _ < rounds; _++) {
			a = Math.round(Math.random() * 0x7);
			b = Math.round(Math.random() * 0x7);
			if (a === b) { b = b + 1 % 0x7; }
			cookie += String.fromCharCode(a | (b << 3) + 0x20);
		} document.cookie = cookie;
	}
	for (let c = 0; rnd < rounds; rnd++) {
		c = cookie.charCodeAt(rnd) - 0x20;
		a = c & 0x7; b = (c >> 3) & 0x7;
		if (!((c >> 6) & 0x1)) { break; }
	}

	// load page
	if (rnd === rounds) {
		const msg = document.createElement("h1");
		msg.classList.add("survey_message")
		msg.innerHTML = "Thank You!";

		survey.style.background = "#212121";
		survey.appendChild(msg);
	} else {	// start survey
		const question= document.createElement("h1");
		question.classList.add("survey_question");
		question.innerHTML = "Click on the most appealing picture";
		const container= document.createElement("div");
		const option_a= document.createElement("div");
		const option_b = document.createElement("div");
		option_a.classList.add("survey_option");
		option_b.classList.add("survey_option");
		option_a.style.background = colors[a];
		option_b.style.background = colors[b];
		option_a.onclick = async () => { await send_result(colors[a], colors[b], true); };
		option_b.onclick = async () => { await send_result(colors[a], colors[b], false); };

		container.appendChild(option_a);
		container.appendChild(option_b);
		survey.appendChild(question);
		survey.appendChild(container);
		// TODO: subject picture
	}
	// TODO: survey pt2.
	// TODO: more data collection
};


async function send_result(a, b, result) {
	for (let i = 0; i < rounds; i++) {
		if (((document.cookie.charCodeAt(i) - 0x20) >> 6) & 0x1) { continue; }
		document.cookie = document.cookie.replaceAt(i, "\x60")
		break;
	}

	await fetch("http://127.0.0.1:80/api/submit_color", {
			method: "POST",
			headers: {
				"Accept":		"application/json",
				"Content-Type":	"application/json"
			},
			body: JSON.stringify({
				"id": 0,
				"color_a": a,
				"color_b": b,
				"chose_a": result,
			})
		})
		.then(response => response.json())
		.then(response => console.log(JSON.stringify(response)))
		.catch((error) => {}
	)

	location.reload();
}
