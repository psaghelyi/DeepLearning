#include "date.hpp"


// Custom exception for invalid dates
bad_date::bad_date(const std::string& message) : std::runtime_error(message) {}


Date Date::create(int year, int month, int day) {
    if (year < 1970 || year > 2038) {
        throw bad_date("Year must be between 1970 and 2038.");
    }
    if (month < 1 || month > 12) {
        throw bad_date("Month must be between 1 and 12.");
    }
    int daysInMonth[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    // Adjust for leap year
    if (month == 2 && ((year % 4 == 0 && year % 100 != 0) || year % 400 == 0)) {
        daysInMonth[1] = 29;
    }
    if (day < 1 || day > daysInMonth[month - 1]) {
        throw bad_date("Invalid day for the given month and year.");
    }
    
    return Date(year, month, day); // Use private constructor
}

bool Date::isValid() const {
    try 
    {
        Date::create(this->getYear(), this->getMonth(), this->getDay());
    } catch (const bad_date& e) {
        return false;
    }
    return true;
}

Date::Date(int year, int month, int day) {
    struct tm date = {}; // Initialize to all zero

    date.tm_year = year - 1900; // tm_year is year since 1900
    date.tm_mon = month - 1; // tm_mon is 0-based
    date.tm_mday = day;

    // convert to epoch time
    epochTime = mktime(&date);
}

// Function to get the year part of the date
int Date::getYear() const {
    struct tm *date = localtime(&epochTime);
    return date->tm_year + 1900; // Convert back to calendar year
}

// Function to get the month part of the date
int Date::getMonth() const {
    struct tm *date = localtime(&epochTime);
    return date->tm_mon + 1; // Convert back to 1-based month
}

// Function to get the day part of the date
int Date::getDay() const {
    struct tm *date = localtime(&epochTime);
    return date->tm_mday;
}

Date::operator bool() const {
    return isValid();
}

