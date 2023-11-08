from threading import Semaphore, Thread
from random import random
from time import sleep

s = Semaphore(1)  # pipet
ls = []  # leader semaphores

def follower(_id: str, l_id: int) -> None:
	ls[l_id].acquire()
	print(f"\tfollower: {_id}")
	sleep(random() * 0.25)  # do something...
	ls[l_id].release()


def leader(_id: int, f_end: Thread) -> None:
	s.acquire()
	print(f"leader: {_id}")
	ls[_id].release()	# open the queue
	f_end.join()		# wait for last follower
	ls[_id].acquire()	# close the queue
	s.release()


if __name__ == "__main__":
	while True:
		ls.clear()
		l = f = None
		for _ in range(10):
			ls.append(Semaphore(0))
			for __ in range(int(random() * 5)):
				f = Thread(target=follower, args=(f"{_}.{__}", _))
				f.start()
			l = Thread(target=leader, args=(_, f))
			l.start()
		l.join()
		print("rendezvous!!!")
		sleep(1)
