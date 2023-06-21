#include "BreadBaker.h"
#include "Program.h"

#include <chrono>
#include <thread>
#include <optional>
#include <iostream>

using namespace std::chrono_literals;


BreadBaker::BreadBaker(
            IOven& oven, ITimer& timer, IKneadMotor& motor, IYeastTray& yeast,
            IExtraIngredientsTray& extras, IDisplay& display,
            IStartButtonLed& startButton, IEventGenerator& eventGenerator,
            Log& log)
    : oven(oven)
    , timer(timer)
    , motor(motor)
    , yeast(yeast)
    , extras(extras)
    , display(display)
    , startButton(startButton)
    , eventGenerator(eventGenerator)
    , log(log)
{
}

bool BreadBaker::Pulse() {
    auto ev = eventGenerator.GetEvent();
    if (ev != std::nullopt) {
        HandleEvent(*ev);
    }
    return ev != std::nullopt;
}


void BreadBaker::reset() {
	oven.Cancel();
	timer.Cancel();
	motor.Stop();
	yeast.Cancel();
	extras.Cancel();
	display.DisplayOff();
	startButton.LedOff();
	state = STANDBY;
}
void BreadBaker::load_program() {
	program.delay =				0;
	program.waiting =			rest_times[program_type];
	program.kneading =			knead_times[program_type];
	program.rising =			rise_times[program_type];
	program.baking =			bake_times[program_type];
	program.yeast =				yeast_times[program_type];
	program.extras =			extra_times[program_type];
	program.total_time =		total_times[program_type];
	program.kneading_cycles =	0;
}


int hours, minutes;  // temp variables to pass to the display
void BreadBaker::HandleEvent(Events ev) {
	if (state == STANDBY)				{ return handle_standby_event(ev); }
	if (ev == MENU_BUTTON_LONG_PRESSED)	{ return reset(); }
	switch (task) {
	case NO_INDICATOR:		return handle_program_select_event(ev);
	case WAITING:			return handle_resting_event(ev);
	case KNEADING:			return handle_kneading_event(ev);
	case RISING:			return handle_rising_event(ev);
	case BAKING:			return handle_baking_event(ev);
	case DONE:				return handle_done_event(ev);
	}
}


void BreadBaker::handle_standby_event(Events ev) {
	if (ev == MENU_BUTTON_PRESSED) {
		state = PROCESSING;
		task = NO_INDICATOR;
		program_type = BREAD_PLAIN;
		load_program();
		display.SetCurrentTask(task);
		display.SetMenu(program_type);
		TIME_REPR(program.total_time, hours, minutes);
		display.SetTime(hours, minutes);
	}
}

void BreadBaker::handle_program_select_event(Events ev) {
	timer.Cancel(); timer.Set(5 MIN);  // (re)set timeout timer
	int delay_max = program_type == BAKE ? 60 : (12 * 60) - program.total_time;

	switch (ev) {
	case MENU_BUTTON_PRESSED:
		program_type = (Program_Type)((program_type + 1) % PROGRAM_COUNT);
		load_program();
		display.SetMenu(program_type);
		TIME_REPR(program.total_time, hours, minutes);
		display.SetTime(hours, minutes);
		return;
	case TIMER_UP_BUTTON_PRESSED:
		program.delay = program.delay + 10 < delay_max ? program.delay + 10 : delay_max;
		TIME_REPR(program.total_time + program.delay, hours, minutes);
		display.SetTime(hours, minutes);
		return;
	case TIMER_DOWN_BUTTON_PRESSED:
		program.delay = program.delay - 10 > 0 ? program.delay - 10 : 0;
		TIME_REPR(program.total_time + program.delay, hours, minutes);
		display.SetTime(hours, minutes);
		return;
	case START_BUTTON_PRESSED:
		if (oven.GetTemperature() >= MAX_OVEN_TEMP) {
			timer.Cancel();  // timer is reset after blocking blink
			for (uint8_t i = 0; i < 10; i++) {  // blink on button led 10x at 1Hz (blocking)
				startButton.LedOn();
				std::this_thread::sleep_for(1000ms);
				startButton.LedOff();
				std::this_thread::sleep_for(1000ms);
			}
			timer.Set(5 MIN);
			return;
		}
		if (program_type == BAKE) {
			timer.Cancel();
			oven.StartBake(program.baking + program.delay);
			task = BAKING; display.SetCurrentTask(task);
			return;
		}
		timer.Cancel();
		timer.Set((program.waiting + program.delay) MIN);
		task = WAITING; display.SetCurrentTask(task);
		return;
	case TIMER_TIMEOUT:				return reset();
	default: return;
	}
}

void BreadBaker::handle_resting_event(Events ev) {
	if (ev != TIMER_TIMEOUT) { return; }
	if (program.yeast > 0)	{ yeast.Drop(program.yeast MS); }
	// extras implementation has a bug where the time is treated as a second instead of a minute (fixed by using MIN instead of the correct MS)
	if (program.extras > 0)	{ extras.Drop(program.extras MIN); }
	task = KNEADING; display.SetCurrentTask(task);
	program.kneading_cycles = 0;
	motor.TurnLeft();
	timer.Set(1 MIN);
}

void BreadBaker::handle_kneading_event(Events ev) {
	if (ev != TIMER_TIMEOUT) { return; }
	program.kneading_cycles++;
	motor.Stop();
	if (program.kneading_cycles < program.kneading) {
		program.kneading_cycles % 2 ? motor.TurnRight() : motor.TurnLeft();
		timer.Set(1 MIN); return;
	}
	task = RISING; display.SetCurrentTask(task);
	oven.StartRise(program.rising);
}

void BreadBaker::handle_rising_event(Events ev) {
	if (ev != OVEN_DONE) { return; }
	if (program_type == DOUGH) {
		task = DONE; display.SetCurrentTask(task);
		timer.Set(5 MIN);
	}
	task = BAKING; display.SetCurrentTask(task);
	oven.StartBake(program.baking);
}

void BreadBaker::handle_baking_event(Events ev) {
	if (ev != OVEN_DONE) { return; }
	task = DONE; display.SetCurrentTask(task);
	timer.Set(5 MIN);
}

void BreadBaker::handle_done_event(Events ev) {
	if (ev != TIMER_TIMEOUT) { return; }
	reset();
}