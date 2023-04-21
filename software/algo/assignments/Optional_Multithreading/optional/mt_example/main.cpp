#include <iostream>
#include <thread>
#include <pthread.h>
#include <vector>
#include <unistd.h>

using namespace std;


void print(int n, const string &str)  {
  string msg = to_string(n) + " : " + str;
  cout << msg  << endl;
}
 
int main() 
{

	int numCPU = sysconf(_SC_NPROCESSORS_ONLN);
  
	cout << "Running on " << numCPU << " cores" << endl;

  	vector<string> s = {
      	"Let's do",
      	"some multithreading",
      	"testing",
      	"and see",
	"what happens"
  	};
  vector<thread> threads;
 
  for (int i = 0; i < s.size(); i++) {
    threads.push_back(thread(print, i, s[i]));
  }
 
  for (auto &th : threads) {
    th.join();
  }
  return 0;
}
