/**
 * constants
 */
const db_url = "http://127.0.0.1:80"
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

const name_input= document.createElement("input");
const age_input= document.createElement("input");
const occupancy_input= document.createElement("input");
const student_input= document.createElement("input");
const gender_input= document.createElement("input");


/**
 * functions
 */
window.onsubmit = async function (event) {
	let cookies = get_cookies();
	await fetch(db_url + "/api/submit_survey", {
		method: "POST",
		headers: {
			"Accept":		"application/json",
			"Content-Type":	"application/json"
		},
		body: JSON.stringify({
			"id":			cookies["id"],
			"age":			age_input.value,
			"name":			name_input.value,
			"male":			gender_input.checked,
			"student":		student_input.checked,
			"occupation":	occupancy_input.value
		})
	});
	set_cookies(cookies["rnd"], cookies["id"], cookies["sf"], "Y");  //status === 200 ? "Y" : "N");
}

window.onload = async function() {
	// handle cookies
	let cookies = get_cookies();

	if (is_empty(cookies)) {
		await start_session();
		location.reload();
	}

	// variables
	let rnd = cookies["rnd"];
	let a, b;  // color indexes
	let round = 0;
	let end;

	for (let c = 0; round < rounds; round++) {
		c = rnd.charCodeAt(round) - 0x20;
		a = c & 0x7; b = (c >> 3) & 0x7;
		if (!((c >> 6) & 0x1)) { break; }
	}

	// load page
	end = round === rounds;
	window.console.log(end, round, cookies)
	if (((!round && cookies["sf"] === "true") ||
		(end && cookies["sf"] === "false")) &&
		cookies["sc"] !== "Y") {
		const background= document.createElement("div");
		const shape_0= document.createElement("div");
		const shape_1= document.createElement("div");
		background.classList.add("background");
		shape_0.classList.add("shape");	background.appendChild(shape_0);
		shape_1.classList.add("shape");	background.appendChild(shape_1);
		const form= document.createElement("form");
		const title= document.createElement("h3");
		title.innerHTML = "Info"; form.appendChild(title);
		const name_label= document.createElement("label");
		name_label.setAttribute("for", "name");
		name_input.setAttribute("type", "text");
		name_label.innerHTML = "Name"; name_input.maxlength = "127";
		name_input.id = "name"; name_input.placeholder = "First and last name";
		form.appendChild(name_label); form.appendChild(name_input);
		const age_label= document.createElement("label");
		age_label.setAttribute("for", "age");
		age_input.setAttribute("type", "number");
		age_label.innerHTML = "Age"; age_input.id = "age"; age_input.placeholder = "Age";
		age_input.min = "16"; age_input.max = "100"
		form.appendChild(age_label); form.appendChild(age_input);
		const occupancy_label= document.createElement("label");
		occupancy_label.setAttribute("for", "occupancy");
		occupancy_input.setAttribute("type", "text");
		occupancy_label.innerHTML = "Occupancy"; occupancy_input.maxlength = "127";
		occupancy_input.id = "occupancy"; occupancy_input.placeholder = "Occupancy";
		form.appendChild(occupancy_label); form.appendChild(occupancy_input);
		const student_label= document.createElement("label");
		student_label.setAttribute("for", "student");
		student_input.setAttribute("type", "checkbox");
		student_label.innerHTML = "Are you a student?"; student_label.id = "student";
		form.appendChild(student_label); form.appendChild(student_input);
		const gender_label= document.createElement("label");
		gender_label.setAttribute("for", "gender");
		gender_input.setAttribute("type", "checkbox");
		gender_label.innerHTML = "Are you male?"; gender_input.id = "gender";
		form.appendChild(gender_label); form.appendChild(gender_input);
		const submit_button= document.createElement("button");
		submit_button.setAttribute("type", "submit");
		submit_button.innerHTML = "Submit"; form.appendChild(submit_button);
		survey.appendChild(background);
		survey.appendChild(form);
	}
	else if (end) {
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
};

function set_cookies(rnd, id, sf, sc = "N") {
	document.cookie = "rnd=" + rnd;
	document.cookie = "id=" + id;
	document.cookie = "sf=" + sf;
	document.cookie = "sc=" + sc;
}

function get_cookies() {
	let decoded = document.cookie.split("; ");
	let dict = {};
	let split;

	decoded.forEach((x) => {
		split = x.split("=");
		if (split[0] === "" || split[1] === "") { return; }
		dict[split[0]] = split[1];
	});
	if (dict["rnd"]) { dict["rnd"].replace("a", "="); }

	return dict;
}

async function start_session() {
	let session = await fetch(db_url + "/api/start", {
		method: "GET",
		headers: {
			"Accept":		"application/json",
			"Content-Type":	"application/json"
		}
	})
	.then(response => response.json())
	.catch((error) => {});

	let rnd = "";
	let a, b;  // color indexes

	for (let _ = 0; _ < rounds; _++) {
		a = Math.round(Math.random() * 0x7);
		b = Math.round(Math.random() * 0x7);
		if (a === b) { b = b + 1 % 0x7; }
		rnd += String.fromCharCode(a | (b << 3) + 0x20);
	} rnd.replace("=", "a");

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

	await fetch(db_url + "/api/submit_color", {
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
	.catch((error) => {})

	location.reload();
}
