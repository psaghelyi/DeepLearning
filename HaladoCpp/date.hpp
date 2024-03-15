// template class to hold date information in year, month, day format
// the internal representation is a single integer (unix epoch)


#ifndef DATE_HPP
#define DATE_HPP

#include <iostream>
#include <string>
#include <vector>
#include <stdexcept>
#include <ctime>

#include "exceptions.hpp"

#define MAX_TRY_RANDOM 10

class Date {   
public:
    // Static factory method for creating Date objects
    static Date create(int year, int month, int day);
    static Date randomDate(const Date &start, const Date &end);
    bool isValid() const;

    Date(int year, int month, int day) : year(year), month(month), day(day) {}

    // Function to get the year part of the date
    int getYear() const { return this->year; }
    int getMonth() const { return this->month; }
    int getDay() const { return this->day; }

    operator bool() const { return isValid(); }
    operator std::string() const;

private:
    int year;
    int month;
    int day;
    void validate() const;
};

#endif