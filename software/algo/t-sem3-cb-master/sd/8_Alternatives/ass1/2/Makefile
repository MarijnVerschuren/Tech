SRC = ass2.c
TARGET = ass2

all : $(SRC)
	$(CC) -g $(SRC) -o $(TARGET)

test : clean $(SRC)
	$(CC) -g $(SRC) -o $(TARGET)
	@./test

clean : 
	rm -f $(TARGET) out*
