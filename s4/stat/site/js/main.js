/**
 * constants
 */
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
	let a, b;  // color indexes for the options
	let lock;  // survey lock to prevent resubmissions

	// handle cookies
	if (document.cookie.length === 0) {
		do {  // create two unique numbers in range (0, 7)
			a = Math.round(Math.random() * 0x7);
			b = Math.round(Math.random() * 0x7);
		} while (a === b);
		document.cookie = String.fromCharCode(a | (b << 3) + 0x20);
	} else {
		let cookie = document.cookie.charCodeAt(0) - 0x20;
		a = cookie & 0x7; b = (cookie >> 3) & 0x7; lock = (cookie >> 6) & 0x1;
	}

	// load page
	if (lock) {
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
		option_a.onclick = () => { send_result(a); };
		option_b.onclick = () => { send_result(b); };

		container.appendChild(option_a);
		container.appendChild(option_b);
		survey.appendChild(question);
		survey.appendChild(container);
		// TODO: subject picture
	}
};


function send_result(result) {
	document.cookie = "\x60"	// update cookie to prevent resubmissions
	// TODO: send result to the database
	window.console.log(result);
	location.reload();
}
