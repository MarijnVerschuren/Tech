#include "linkedList.h"
#include "gtest/gtest.h"
 
class linkedListTest : public ::testing::Test {
 protected:
  virtual void SetUp() {
  }
 
  virtual void TearDown() {
    // Code here will be called immediately after each test
    // (right before the destructor).
  }
};
 
TEST_F(linkedListTest,addFirst){
    linkedList list;
    EXPECT_EQ(0,list.addFirst(1));
    EXPECT_EQ(0,list.addFirst(2));
    EXPECT_EQ(2,list.getHeadValue());
    EXPECT_EQ(1,list.getTailValue());
    list.showList();
}

