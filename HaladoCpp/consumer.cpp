#include "consumer.hpp"

int consumer(Date const &date)
{
    static Date previousDate(-1, -1, -1);
    Date _date = previousDate;
    previousDate = date;

    if (_date.getYear() == -1) {
        return 42;
    }
    if (date < _date) {
        return -1;
    }
    if (date > _date) {
        return 1;
    }
    return 0;
}

ConsumerFunction consumerFunction = consumer;
