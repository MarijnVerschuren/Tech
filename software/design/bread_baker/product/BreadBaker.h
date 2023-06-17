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

    // For testing purposes
    // You'll have to decide yourself if you'd rather:
    // - have these methods private (better encapsulation)
    // - be able to test these methods
    // You cannot have both at the same time (without dirty tricks)
    void HandleEvent(Events ev);

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

	Program program;
	Tasks task = NO_INDICATOR;
	uint32_t program_time;
	uint8_t program_type = 0;
	uint8_t knead_cycles = 0;
	uint32_t timer_max = 0;
	uint32_t timer_time = 0;
	bool awake = false;
};

#endif
