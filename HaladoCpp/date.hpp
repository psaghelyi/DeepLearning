// template class to hold date information in year, month, day format
// the internal representation is a single integer (unix epoch)


#ifndef DATE_HPP
#define DATE_HPP

#include <iostream>
#include <string>
#include <stdexcept>
#include <ctime>

// Custom exception for invalid dates
class bad_date : public std::runtime_error {
public:
    bad_date(const std::string& message);
};

class Date {   
public:
    // Static factory method for creating Date objects
    static Date create(int year, int month, int day);
    bool isValid() const;

    Date(int year, int month, int day);

    // Function to get the year part of the date
    int getYear() const;
    int getMonth() const;
    int getDay() const;

    operator bool() const;

private:
    time_t epochTime; // Stores the date as Unix epoch time
};

#endif