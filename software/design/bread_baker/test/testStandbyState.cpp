#include "BreadBaker.h"
#include "BrokenLog.h"
#include "MDisplay.h"
#include "MEventGenerator.h"
#include "MExtraIngredientsTray.h"
#include "MKneadMotor.h"
#include "MOven.h"
#include "MStartButtonLed.h"
#include "MTimer.h"
#include "MYeastTray.h"
#include "TimeConstants.h"

using ::testing::Return;
using ::testing::_;

class StateTest: public ::testing::Test
{
protected:
    StateTest()
    {
        baker = new BreadBaker(
                    oven, timer, motor, yeast, extras,
                    display, startButton, event, log);
    }

    virtual ~StateTest()
    {
        delete baker;
        baker = nullptr;
    }

    MDisplay display;
    MEventGenerator event;
    MExtraIngredientsTray extras;
    MKneadMotor motor;
    MOven oven;
    MStartButtonLed startButton;
    MTimer timer;
    MYeastTray yeast;

    BrokenLog log;
    BreadBaker* baker;
};


TEST_F(StateTest, test_plain_bread_timer_change) {
	EXPECT_CALL(display, SetCurrentTask(NO_INDICATOR)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(WAITING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(KNEADING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(RISING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(BAKING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(DONE)).Times(1);

	EXPECT_CALL(display, SetMenu(BREAD_PLAIN)).Times(1);
	EXPECT_CALL(display, SetTime(4, 50)).Times(1);
	EXPECT_CALL(display, SetTime(5, 0)).Times(2);  // timer up / down
	EXPECT_CALL(display, SetTime(5, 10)).Times(1);  // timer up
    EXPECT_CALL(display, DisplayOff()).Times(1);  // when resetting

    EXPECT_CALL(event, GetEvent()).Times(0);  // not used

	EXPECT_CALL(extras, Drop(extra_times[BREAD_PLAIN] MIN)).Times(0);
    EXPECT_CALL(extras, Cancel()).Times(1);  // when resetting

	EXPECT_CALL(motor, TurnLeft()).Times((int)(knead_times[BREAD_PLAIN] / 2));
	EXPECT_CALL(motor, TurnRight()).Times((int)(knead_times[BREAD_PLAIN] / 2));
	EXPECT_CALL(motor, Stop()).Times(knead_times[BREAD_PLAIN] + 1);  // once when resetting

    EXPECT_CALL(oven, StartRise(rise_times[BREAD_PLAIN])).Times(1);
    EXPECT_CALL(oven, StartBake(bake_times[BREAD_PLAIN])).Times(1);
    EXPECT_CALL(oven, IsOn()).Times(0);
    EXPECT_CALL(oven, GetTemperature()).Times(1);
    EXPECT_CALL(oven, Cancel()).Times(1);  // when resetting

    EXPECT_CALL(startButton, LedOn()).Times(0);
    EXPECT_CALL(startButton, LedOff()).Times(1);  // when resetting

    EXPECT_CALL(timer, Set(_)).Times(knead_times[BREAD_PLAIN] + 6);
    EXPECT_CALL(timer, Cancel()).Times(6);  // 5 events within program_select and once when resetting

    EXPECT_CALL(yeast, Drop(yeast_times[BREAD_PLAIN] * 1000)).Times(1);
    EXPECT_CALL(yeast, Cancel()).Times(1);  // when resetting

	baker->HandleEvent(MENU_BUTTON_PRESSED);  // plain bread
	baker->HandleEvent(TIMER_UP_BUTTON_PRESSED);
	baker->HandleEvent(TIMER_UP_BUTTON_PRESSED);
	baker->HandleEvent(TIMER_DOWN_BUTTON_PRESSED);
	baker->HandleEvent(START_BUTTON_PRESSED);
	baker->HandleEvent(TIMER_TIMEOUT);  // resting
	for (uint8_t i = 0; i < knead_times[BREAD_PLAIN]; i++) {
		baker->HandleEvent(TIMER_TIMEOUT);  // kneading
	}
	baker->HandleEvent(OVEN_DONE);  // rising
	baker->HandleEvent(OVEN_DONE);  // baking
	baker->HandleEvent(TIMER_TIMEOUT);  // done

    EXPECT_EQ(0, 0); // a Google test project must have at least one EXPECT_... or ASSERT_..., else it won't compile
}
TEST_F(StateTest, test_bread_plus) {
	EXPECT_CALL(display, SetCurrentTask(NO_INDICATOR)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(WAITING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(KNEADING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(RISING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(BAKING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(DONE)).Times(1);

	EXPECT_CALL(display, SetMenu(BREAD_PLAIN)).Times(1);
	EXPECT_CALL(display, SetMenu(BREAD_PLUS)).Times(1);
	EXPECT_CALL(display, SetTime(4, 50)).Times(2);
	EXPECT_CALL(display, DisplayOff()).Times(1);  // when resetting

	EXPECT_CALL(event, GetEvent()).Times(0);  // not used

	EXPECT_CALL(extras, Drop(extra_times[BREAD_PLUS] MIN)).Times(1);
	EXPECT_CALL(extras, Cancel()).Times(1);  // when resetting

	EXPECT_CALL(motor, TurnLeft()).Times((int)(knead_times[BREAD_PLUS] / 2));
	EXPECT_CALL(motor, TurnRight()).Times((int)(knead_times[BREAD_PLUS] / 2));
	EXPECT_CALL(motor, Stop()).Times(knead_times[BREAD_PLUS] + 1);  // once when resetting

	EXPECT_CALL(oven, StartRise(rise_times[BREAD_PLUS])).Times(1);
	EXPECT_CALL(oven, StartBake(bake_times[BREAD_PLUS])).Times(1);
	EXPECT_CALL(oven, IsOn()).Times(0);
	EXPECT_CALL(oven, GetTemperature()).Times(1);
	EXPECT_CALL(oven, Cancel()).Times(1);  // when resetting

	EXPECT_CALL(startButton, LedOn()).Times(0);
	EXPECT_CALL(startButton, LedOff()).Times(1);  // when resetting

	EXPECT_CALL(timer, Set(_)).Times(knead_times[BREAD_PLUS] + 4);
	EXPECT_CALL(timer, Cancel()).Times(4);  // 3 events within program_select and once when resetting

	EXPECT_CALL(yeast, Drop(yeast_times[BREAD_PLUS] * 1000)).Times(1);
	EXPECT_CALL(yeast, Cancel()).Times(1);  // when resetting

	baker->HandleEvent(MENU_BUTTON_PRESSED);  // plain bread
	baker->HandleEvent(MENU_BUTTON_PRESSED);  // bread +
	baker->HandleEvent(START_BUTTON_PRESSED);
	baker->HandleEvent(TIMER_TIMEOUT);  // resting
	for (uint8_t i = 0; i < knead_times[BREAD_PLUS]; i++) {
		baker->HandleEvent(TIMER_TIMEOUT);  // kneading
	}
	baker->HandleEvent(OVEN_DONE);  // rising
	baker->HandleEvent(OVEN_DONE);  // baking
	baker->HandleEvent(TIMER_TIMEOUT);  // done

	EXPECT_EQ(0, 0); // a Google test project must have at least one EXPECT_... or ASSERT_..., else it won't compile
}
TEST_F(StateTest, test_rapid) {
	EXPECT_CALL(display, SetCurrentTask(NO_INDICATOR)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(WAITING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(KNEADING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(RISING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(BAKING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(DONE)).Times(1);

	EXPECT_CALL(display, SetMenu(BREAD_PLAIN)).Times(1);
	EXPECT_CALL(display, SetMenu(BREAD_PLUS)).Times(1);
	EXPECT_CALL(display, SetMenu(RAPID)).Times(1);
	EXPECT_CALL(display, SetTime(4, 50)).Times(2);  // BREAD_PLAIN, BREAD_PLUS
	EXPECT_CALL(display, SetTime(1, 55)).Times(1);  // RAPID
	EXPECT_CALL(display, DisplayOff()).Times(1);  // when resetting

	EXPECT_CALL(event, GetEvent()).Times(0);  // not used

	EXPECT_CALL(extras, Drop(extra_times[RAPID] MIN)).Times(0);
	EXPECT_CALL(extras, Cancel()).Times(1);  // when resetting

	EXPECT_CALL(motor, TurnLeft()).Times((int)(knead_times[RAPID] / 2) + 1);
	EXPECT_CALL(motor, TurnRight()).Times((int)(knead_times[RAPID] / 2));
	EXPECT_CALL(motor, Stop()).Times(knead_times[RAPID] + 1);  // once when resetting

	EXPECT_CALL(oven, StartRise(rise_times[RAPID])).Times(1);
	EXPECT_CALL(oven, StartBake(bake_times[RAPID])).Times(1);
	EXPECT_CALL(oven, IsOn()).Times(0);
	EXPECT_CALL(oven, GetTemperature()).Times(1);
	EXPECT_CALL(oven, Cancel()).Times(1);  // when resetting

	EXPECT_CALL(startButton, LedOn()).Times(0);
	EXPECT_CALL(startButton, LedOff()).Times(1);  // when resetting

	EXPECT_CALL(timer, Set(_)).Times(knead_times[RAPID] + 5);
	EXPECT_CALL(timer, Cancel()).Times(5);  // 4 events within program_select and once when resetting

	EXPECT_CALL(yeast, Drop(yeast_times[RAPID] * 1000)).Times(1);
	EXPECT_CALL(yeast, Cancel()).Times(1);  // when resetting

	baker->HandleEvent(MENU_BUTTON_PRESSED);  // plain bread
	baker->HandleEvent(MENU_BUTTON_PRESSED);  // bread +
	baker->HandleEvent(MENU_BUTTON_PRESSED);  // rapid
	baker->HandleEvent(START_BUTTON_PRESSED);
	baker->HandleEvent(TIMER_TIMEOUT);  // resting
	for (uint8_t i = 0; i < knead_times[RAPID]; i++) {
		baker->HandleEvent(TIMER_TIMEOUT);  // kneading
	}
	baker->HandleEvent(OVEN_DONE);  // rising
	baker->HandleEvent(OVEN_DONE);  // baking
	baker->HandleEvent(TIMER_TIMEOUT);  // done

	EXPECT_EQ(0, 0); // a Google test project must have at least one EXPECT_... or ASSERT_..., else it won't compile
}
TEST_F(StateTest, test_dough) {
	EXPECT_CALL(display, SetCurrentTask(NO_INDICATOR)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(WAITING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(KNEADING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(RISING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(BAKING)).Times(0);
	EXPECT_CALL(display, SetCurrentTask(DONE)).Times(1);

	EXPECT_CALL(display, SetMenu(BREAD_PLAIN)).Times(1);
	EXPECT_CALL(display, SetMenu(BREAD_PLUS)).Times(1);
	EXPECT_CALL(display, SetMenu(RAPID)).Times(1);
	EXPECT_CALL(display, SetMenu(DOUGH)).Times(1);
	EXPECT_CALL(display, SetTime(4, 50)).Times(2);  // BREAD_PLAIN, BREAD_PLUS
	EXPECT_CALL(display, SetTime(1, 55)).Times(1);  // RAPID
	EXPECT_CALL(display, SetTime(2, 20)).Times(1);  // DOUGH
	EXPECT_CALL(display, DisplayOff()).Times(1);  // when resetting

	EXPECT_CALL(event, GetEvent()).Times(0);  // not used

	EXPECT_CALL(extras, Drop(extra_times[DOUGH] MIN)).Times(0);
	EXPECT_CALL(extras, Cancel()).Times(1);  // when resetting

	EXPECT_CALL(motor, TurnLeft()).Times((int)(knead_times[DOUGH] / 2));
	EXPECT_CALL(motor, TurnRight()).Times((int)(knead_times[DOUGH] / 2));
	EXPECT_CALL(motor, Stop()).Times(knead_times[DOUGH] + 1);  // once when resetting

	EXPECT_CALL(oven, StartRise(rise_times[DOUGH])).Times(1);
	EXPECT_CALL(oven, StartBake(bake_times[DOUGH])).Times(0);
	EXPECT_CALL(oven, IsOn()).Times(0);
	EXPECT_CALL(oven, GetTemperature()).Times(1);
	EXPECT_CALL(oven, Cancel()).Times(1);  // when resetting

	EXPECT_CALL(startButton, LedOn()).Times(0);
	EXPECT_CALL(startButton, LedOff()).Times(1);  // when resetting

	EXPECT_CALL(timer, Set(_)).Times(knead_times[DOUGH] + 6);
	EXPECT_CALL(timer, Cancel()).Times(6);  // 5 events within program_select and once when resetting

	EXPECT_CALL(yeast, Drop(yeast_times[DOUGH] * 1000)).Times(1);
	EXPECT_CALL(yeast, Cancel()).Times(1);  // when resetting

	baker->HandleEvent(MENU_BUTTON_PRESSED);  // plain bread
	baker->HandleEvent(MENU_BUTTON_PRESSED);  // bread +
	baker->HandleEvent(MENU_BUTTON_PRESSED);  // rapid
	baker->HandleEvent(MENU_BUTTON_PRESSED);  // dough
	baker->HandleEvent(START_BUTTON_PRESSED);
	baker->HandleEvent(TIMER_TIMEOUT);  // resting
	for (uint8_t i = 0; i < knead_times[DOUGH]; i++) {
	baker->HandleEvent(TIMER_TIMEOUT);  // kneading
	}
	baker->HandleEvent(OVEN_DONE);  // rising
	baker->HandleEvent(TIMER_TIMEOUT);  // done

	EXPECT_EQ(0, 0); // a Google test project must have at least one EXPECT_... or ASSERT_..., else it won't compile
}
TEST_F(StateTest, test_bake_time_change) {
	EXPECT_CALL(display, SetCurrentTask(NO_INDICATOR)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(WAITING)).Times(0);
	EXPECT_CALL(display, SetCurrentTask(KNEADING)).Times(0);
	EXPECT_CALL(display, SetCurrentTask(RISING)).Times(0);
	EXPECT_CALL(display, SetCurrentTask(BAKING)).Times(1);
	EXPECT_CALL(display, SetCurrentTask(DONE)).Times(1);

	EXPECT_CALL(display, SetMenu(BREAD_PLAIN)).Times(1);
	EXPECT_CALL(display, SetMenu(BREAD_PLUS)).Times(1);
	EXPECT_CALL(display, SetMenu(RAPID)).Times(1);
	EXPECT_CALL(display, SetMenu(DOUGH)).Times(1);
	EXPECT_CALL(display, SetMenu(BAKING)).Times(1);
	EXPECT_CALL(display, SetTime(4, 50)).Times(2);  // BREAD_PLAIN, BREAD_PLUS
	EXPECT_CALL(display, SetTime(1, 55)).Times(1);  // RAPID
	EXPECT_CALL(display, SetTime(2, 20)).Times(1);  // DOUGH
	EXPECT_CALL(display, SetTime(0, 30)).Times(1);  // BAKE
	EXPECT_CALL(display, SetTime(0, 40)).Times(2);  // TIMER UP / DOWN
	EXPECT_CALL(display, SetTime(0, 50)).Times(1);  // TIMER UP
	EXPECT_CALL(display, DisplayOff()).Times(1);  // when resetting

	EXPECT_CALL(event, GetEvent()).Times(0);  // not used

	EXPECT_CALL(extras, Drop(extra_times[BAKE] MIN)).Times(0);
	EXPECT_CALL(extras, Cancel()).Times(1);  // when resetting

	EXPECT_CALL(motor, TurnLeft()).Times(0);
	EXPECT_CALL(motor, TurnRight()).Times(0);
	EXPECT_CALL(motor, Stop()).Times(1);  // once when resetting

	EXPECT_CALL(oven, StartRise(rise_times[BAKE])).Times(0);
	EXPECT_CALL(oven, StartBake(bake_times[BAKE] + 10)).Times(1);  // timer was changed
	EXPECT_CALL(oven, IsOn()).Times(0);
	EXPECT_CALL(oven, GetTemperature()).Times(1);
	EXPECT_CALL(oven, Cancel()).Times(1);  // when resetting

	EXPECT_CALL(startButton, LedOn()).Times(0);
	EXPECT_CALL(startButton, LedOff()).Times(1);  // when resetting

	EXPECT_CALL(timer, Set(_)).Times(9);
	EXPECT_CALL(timer, Cancel()).Times(10);  // 9 events within program_select and once when resetting

	EXPECT_CALL(yeast, Drop(yeast_times[BAKE] * 1000)).Times(0);
	EXPECT_CALL(yeast, Cancel()).Times(1);  // when resetting

	baker->HandleEvent(MENU_BUTTON_PRESSED);  // plain bread
	baker->HandleEvent(MENU_BUTTON_PRESSED);  // bread +
	baker->HandleEvent(MENU_BUTTON_PRESSED);  // rapid
	baker->HandleEvent(MENU_BUTTON_PRESSED);  // dough
	baker->HandleEvent(MENU_BUTTON_PRESSED);  // bake
	baker->HandleEvent(TIMER_UP_BUTTON_PRESSED);
	baker->HandleEvent(TIMER_UP_BUTTON_PRESSED);
	baker->HandleEvent(TIMER_DOWN_BUTTON_PRESSED);
	baker->HandleEvent(START_BUTTON_PRESSED);
	baker->HandleEvent(OVEN_DONE);  // baking
	baker->HandleEvent(TIMER_TIMEOUT);  // done

	EXPECT_EQ(0, 0); // a Google test project must have at least one EXPECT_... or ASSERT_..., else it won't compile
}
// OVEN TEMP FAIL TEST (cannot set oven temp)