#ifndef __LINKEDLISTH__
#define __LINKEDLISTH__

struct item
{
    int value=0;
    public:
    static int counter;
    item *next;
    int getValue();
};

class linkedList
{
private:
    item *head,*tail;
public:
    linkedList()
    {
        head = 0;
        tail = 0;
    }

    int addFirst(int value);
    void showList();
    int getHeadValue();
    int getTailValue();
};

#endif

