#include "date.hpp"

#include <sstream>


Date Date::create(int year, int month, int day) {
        Date date(year, month, day);
        return date;
}

Date::operator std::string() const
{
    std::ostringstream oss;
    oss << this->year << "-" << this->month << "-" << this->day;
    return oss.str();
}

void Date::validate() const {
    if (this->year < 1970 || this->year > 2038) {
        throw bad_date("Year must be between 1970 and 2038.");
    }
    if (this->month < 1 || this->month > 12) {
        throw bad_date("Month must be between 1 and 12.");
    }
    int daysInMonth[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    // Adjust for leap year
    if (this->month == 2 && ((this->year % 4 == 0 && this->year % 100 != 0) || this->year % 400 == 0)) {
        daysInMonth[1] = 29;
    }
    if (this->day < 1 || this->day > daysInMonth[month - 1]) {
        throw bad_date("Invalid day for the given month and year.");
    }
}

bool Date::isValid() const {
    try 
    {
        this->validate();
    } catch (const bad_date& e) {
        return false;
    } catch (...) {
        throw;
    }
    return true;
}


// Egy véletlen dátum generálása a megadott intervallumban
Date Date::randomDate(const Date &start, const Date &end) {
    #ifdef DEBUG
    std::vector<std::string> dates(MAX_TRY_RANDOM);
#endif

    for (int i = 0; i < MAX_TRY_RANDOM; ++i) {
        int year = 1970 + std::rand() % (2038 - 1970 + 1);
        int month = 1 + std::rand() % 12;
        int day = 1 + std::rand() % 31;

        Date date = Date::create(year, month, day);
        
#ifdef DEBUG
        dates.push_back(date);
#endif

        if (date.isValid()) {
            return date;
        }
    }

#ifdef DEBUG
    std::cerr << "Failed to generate a valid random date. Tried the following dates: ";
    for (std::vector<std::string>::const_iterator it = dates.begin(); it != dates.end(); ++it) {
        std::cerr << *it << " ";
    }
    std::cerr << std::endl;
#endif

    throw terrible_random("Failed to generate a valid random date.");
}
