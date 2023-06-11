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
		display.SetCurrentTask(task);
		display.SetMenu(program_type);
		program_time = total_times[program_type];
		program_time.get(hours, minutes);
		display.SetTime(hours, minutes);
		program.waiting = rest_times[program_type].time;
		program.kneading = knead_times[program_type].time;
		program.rising = rise_times[program_type].time;
		program.baking = bake_times[program_type].time;
		program.addYeast = false;  // TODO: recipes
		program.addExtras = false;  // TODO: recipes
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
		pre_start_wait = (pre_start_wait + 10) % (12 * 60 + 10);  // max is 12h (10 is added so that 12h is allowed)
		program_time.additional_time = pre_start_wait;
		program_time.get(hours, minutes);
		display.SetTime(hours, minutes);
		timer.Cancel(); timer.Set(5 MIN);  // (re)set timeout timer
		break;
	case TIMER_DOWN_BUTTON_PRESSED:
		pre_start_wait = pre_start_wait ? pre_start_wait - 10 : 12 * 60;
		program_time.additional_time = pre_start_wait;
		program_time.get(hours, minutes);
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
			}
			break;
		}
		timer.Cancel();

		// TODO: start everything
		break;
	case OVEN_DONE:
		// TODO: notify
		timer.Cancel(); timer.Set(5 MIN);  // (re)set timeout timer
		break;
	case TIMER_TIMEOUT:
		timer.Cancel();
		oven.Cancel();
		motor.Stop();
		yeast.Cancel();
		extras.Cancel();
		display.DisplayOff();
		awake = false;
		break;
	default:  // NO_EVENT_OCCURRED
		break;
	}
}
