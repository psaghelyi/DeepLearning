#ifndef DATE_HPP
#define DATE_HPP

#include <iostream>
#include <string>
#include <vector>
#include <stdexcept>
#include <ctime>
#include <tuple>

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

    bool operator<(const Date& other) const 
    { 
        return std::tie(this->year, this->month, this->day) < 
                std::tie(other.year, other.month, other.day);
    }
    
    bool operator==(const Date& other) const 
    { 
        return std::tie(this->year, this->month, this->day) == 
                std::tie(other.year, other.month, other.day);
    }
    
    bool operator>(const Date& other) const 
    {
        return !(*this < other || *this == other);
    }
    
    bool operator<=(const Date& other) const 
    {
        return *this < other || *this == other;
    }

    bool operator>=(const Date& other) const 
    {
        return !(*this < other);
    }
    
    bool operator!=(const Date& other) const 
    {
        return !(*this == other);
    }

    friend std::ostream& operator<<(std::ostream& os, const Date& date) {
        os << date.getYear() << " " << date.getMonth() << " " << date.getDay();
        return os;
    }
    

private:
    int year;
    int month;
    int day;
    void validate() const;
};

#endif