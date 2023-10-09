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
function is_empty(obj) {
  return Object.keys(obj).length === 0;
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
window.onload = async function() {
	// handle cookies
	let cookies = get_cookies();
	window.console.log(cookies);
	window.console.log(is_empty(cookies));

	if (is_empty(cookies)) {
		await start_session();
	}

	// variables
	let rnd = cookies["rnd"];
	let a, b;  // color indexes
	let round = 0;

	for (let c = 0; round < rounds; round++) {
		c = rnd.charCodeAt(round) - 0x20;
		a = c & 0x7; b = (c >> 3) & 0x7;
		if (!((c >> 6) & 0x1)) { break; }
	}

	// load page
	if (round === rounds) {
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
	}
	// TODO: survey pt2.
};

function set_cookies(rnd, id, sf) {
	document.cookie = "rnd=" + rnd;
	document.cookie = "id=" + id;
	document.cookie = "sf=" + sf;
}

function get_cookies() {
	let decoded = decodeURIComponent(document.cookie).split("; ");
	let dict = {};
	let split;

	decoded.forEach((x) => {
		split = x.split("=");
		if (split[0] === "" || split[1] === "") { return; }
		dict[split[0]] = split[1];
	})

	return dict;
}

async function start_session() {
	let session = await fetch("http://127.0.0.1:80/api/start", {
			method: "GET",
			headers: {
				"Accept":		"application/json",
				"Content-Type":	"application/json"
			}
		})
		.then(response => response.json())
		.catch((error) => {}
	);

	let rnd = "";
	let a, b;  // color indexes

	for (let _ = 0; _ < rounds; _++) {
		a = Math.round(Math.random() * 0x7);
		b = Math.round(Math.random() * 0x7);
		if (a === b) { b = b + 1 % 0x7; }
		rnd += String.fromCharCode(a | (b << 3) + 0x20);
	}

	set_cookies(rnd, session["id"], session["survey_first"]);
}

async function send_result(a, b, result) {
	let cookies = get_cookies();
	let rnd = cookies["rnd"];
	let id = cookies["id"];

	for (let i = 0; i < rounds; i++) {
		if (((rnd.charCodeAt(i) - 0x20) >> 6) & 0x1) { continue; }
		rnd = rnd.replaceAt(i, "\x60")
		break;
	}

	set_cookies(rnd, id, cookies["sf"]);

	await fetch("http://127.0.0.1:80/api/submit_color", {
			method: "POST",
			headers: {
				"Accept":		"application/json",
				"Content-Type":	"application/json"
			},
			body: JSON.stringify({
				"id": id,
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
