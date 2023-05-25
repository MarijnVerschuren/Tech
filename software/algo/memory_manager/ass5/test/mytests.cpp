
#include "MemoryManager.h"
#include "MList.h"
#include "gtest/gtest.h"

class metaTest : public ::testing::Test {
 protected:
  virtual void SetUp() {
  }
 
  virtual void TearDown() {
    // Code here will be called immediately after each test
    // (right before the destructor).
  }
};

/* A simple example of Unit Test */
TEST_F(metaTest,testClaim)
{
  MemoryManager *mm = new MemoryManager();
  // Execute once the code is implemented 
  //
  //int ret = mm->claimMemory(20);
  //EXPECT_EQ(mm->memStart, ret);
  //EXPECT_EQ(mm->memStart, mm->allocList->head->_addr);
  //EXPECT_EQ(20, mm->allocList->head->_size);
  delete mm;
}


