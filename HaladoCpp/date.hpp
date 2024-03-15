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

    Date(int year, int month, int day) : data(year, month, day) { }

    // Function to get the year part of the date
    int getYear() const { return std::get<0>(data); }
    int getMonth() const { return std::get<1>(data); }
    int getDay() const { return std::get<2>(data); }

    operator bool() const { return isValid(); }

    bool operator<(const Date& other) const { return data < other.data; }
    bool operator==(const Date& other) const { return data == other.data; }
    bool operator>(const Date& other) const { return !(*this < other || *this == other); }    
    bool operator<=(const Date& other) const { return *this < other || *this == other; }
    bool operator>=(const Date& other) const { return !(*this < other); }
    bool operator!=(const Date& other) const { return !(*this == other); }

    friend std::ostream& operator<<(std::ostream& os, const Date& date) {
        os << date.getYear() << " " << date.getMonth() << " " << date.getDay();
        return os;
    }

private:
    // a dátumot egy tupple-ben tároljuk a sok összehasonlítás miatt
    std::tuple<int, int, int> data;
    void validate() const;
};

#endif