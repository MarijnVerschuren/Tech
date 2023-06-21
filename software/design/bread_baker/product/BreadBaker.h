#ifndef BREADBAKER_H
#define BREADBAKER_H

#include "Events.h"
#include "IDisplay.h"
#include "IEventGenerator.h"
#include "IExtraIngredientsTray.h"
#include "IKneadMotor.h"
#include "IOven.h"
#include "IStartButtonLed.h"
#include "ITimer.h"
#include "IYeastTray.h"
#include "Log.h"
#include "States.h"
#include "TimeConstants.h"
#include "Program.h"

class BreadBaker
{
public:
    BreadBaker(IOven& oven, ITimer& timer, IKneadMotor& motor,
               IYeastTray& yeast, IExtraIngredientsTray& extras,
               IDisplay& display, IStartButtonLed& startButton,
               IEventGenerator& eventGenerator, Log& log);

    BreadBaker(const BreadBaker& other) = delete;
    BreadBaker& operator=(const BreadBaker&) = delete;

    bool Pulse();

	void reset();
	void load_program();
    // For testing purposes
    // You'll have to decide yourself if you'd rather:
    // - have these methods private (better encapsulation)
    // - be able to test these methods
    // You cannot have both at the same time (without dirty tricks)
    void HandleEvent(Events ev);

	void handle_standby_event(Events ev);
	void handle_program_select_event(Events ev);
	void handle_resting_event(Events ev);
	void handle_kneading_event(Events ev);
	void handle_rising_event(Events ev);
	void handle_baking_event(Events ev);
	void handle_done_event(Events ev);

private:
    IOven& oven;
    ITimer& timer;
    IKneadMotor& motor;
    IYeastTray& yeast;
    IExtraIngredientsTray& extras;
    IDisplay& display;
    IStartButtonLed& startButton;
    IEventGenerator& eventGenerator;
    Log& log;

	Program_Type program_type;
	Program program;
	States state = STANDBY;
	Tasks task = NO_INDICATOR;
};

#endif
