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

// parameter name in comment to prevent compiler warning as it is unused for now
void BreadBaker::HandleEvent(Events ev) {
	uint32_t hours, minutes;
	switch (ev) {
	case MENU_BUTTON_PRESSED:
		if (!awake) {
			awake = true; // wake machine? TODO
			program_type = 0;
		} else {
			program_type = (program_type + 1) % 5;
		}
		timer_max = program_type == 4 ? 60 : 12 * 60;  // timer can be 60m when bake only is selected otherwise it can be 12h
		display.SetCurrentTask(task);
		display.SetMenu(program_type);
		program_time = total_times[program_type];
		hours = (timer_time + program_time) / 60;
		minutes = (timer_time + program_time) % 60;
		display.SetTime(hours, minutes);
		program.waiting = rest_times[program_type];
		program.kneading = knead_times[program_type];
		program.rising = rise_times[program_type];
		program.baking = bake_times[program_type];
		if (bake_times[program_type] == 0xffffffff) { program.baking = 0; }
		program.addYeast = yeast_times[program_type] != 0xffffffff;
		program.addExtras = extra_times[program_type] != 0xffffffff;
		timer.Cancel(); timer.Set(5 MIN);  // (re)set timeout timer
		break;
	case MENU_BUTTON_LONG_PRESSED:
		timer.Cancel();
		oven.Cancel();
		motor.Stop();
		yeast.Cancel();
		extras.Cancel();
		display.DisplayOff();
		awake = false;
		break;
	case TIMER_UP_BUTTON_PRESSED:
		timer_time = (timer_time + 10) % (timer_max + 10);  // inc is added to max to allow max as a setting
		hours = (timer_time + program_time) / 60;
		minutes = (timer_time + program_time) % 60;
		display.SetTime(hours, minutes);
		timer.Cancel(); timer.Set(5 MIN);  // (re)set timeout timer
		break;
	case TIMER_DOWN_BUTTON_PRESSED:
		if (timer_time) { timer_time -= 10; }
		else { timer_time = timer_max; }
		hours = (timer_time + program_time) / 60;
		minutes = (timer_time + program_time) % 60;
		display.SetTime(hours, minutes);
		timer.Cancel(); timer.Set(5 MIN);  // (re)set timeout timer
		break;
	case START_BUTTON_PRESSED:
		if (oven.GetTemperature() >= 50) {
			for (uint8_t i = 0; i < 10; i++) {  // blink on button led 10x at 1Hz (blocking)
				startButton.LedOn();
				std::this_thread::sleep_for(500ms);
				startButton.LedOff();
				std::this_thread::sleep_for(500ms);
			} break;
		}
		timer.Cancel();
		if (program_type == 4) {
			task = BAKING;
			timer.Set((program.baking + timer_time) MIN);
		} else {
			task = WAITING;
			timer.Set((program.waiting + timer_time) MIN);  // set rest timer + time specified by user
		}
		break;
	case OVEN_DONE:
		// TODO: DONE
		timer.Cancel(); timer.Set(5 MIN);  // (re)set timeout timer
		break;
	case TIMER_TIMEOUT:
		switch (task) {
		case Tasks::NO_INDICATOR:
			timer.Cancel();
			oven.Cancel();
			motor.Stop();
			yeast.Cancel();
			extras.Cancel();
			display.DisplayOff();
			awake = false;
			break;
		case Tasks::WAITING:
			knead_cycles = 0;
			motor.TurnLeft();
			task = KNEADING;
			if (program.addYeast) {
				yeast.Drop(yeast_times[program_type] * 1000);  // schedule yeast addition (in ms?)
			}
			if (program.addExtras) {
				extras.Drop(extra_times[program_type] MIN);  // schedule extras addition
			}
			timer.Set(1 MIN);  // kneading has to switch every minute
			break;
		case Tasks::KNEADING:
			if (knead_cycles == program.kneading) {
				task = RISING;
				timer.Set(program.rising MIN);  // set rising timer
				break;
			}
			motor.Stop();
			knead_cycles % 2 ? motor.TurnLeft() : motor.TurnRight();
			knead_cycles++;
			timer.Set(1 MIN);  // reset kneading timer
			break;
		case Tasks::RISING:
			if (!program.baking) {  // dough only
				// TODO: DONE
				break;
			}
			task = BAKING;
			timer.Set(program.baking MIN);
			break;
		case Tasks::BAKING:
			// TODO: DONE
			break;
		default:
			break;
		}
	default:  // NO_EVENT_OCCURRED
		break;
	}
}
