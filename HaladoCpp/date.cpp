#include "date.hpp"

#include <sstream>


Date Date::create(int year, int month, int day) {
    Date date(year, month, day);
    date.validate();
    return date;
}

void Date::validate() const {
    if (getYear() < 1970 || getYear() > 2038) {
        throw bad_date("Year must be between 1970 and 2038.");
    }
    if (getMonth() < 1 || getMonth() > 12) {
        throw bad_date("Month must be between 1 and 12.");
    }
    int daysInMonth[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    // Adjust for leap year
    if (getMonth() == 2 && ((getYear() % 4 == 0 && getYear() % 100 != 0) || getYear() % 400 == 0)) {
        daysInMonth[1] = 29;
    }
    if (getDay() < 1 || getDay() > daysInMonth[getMonth() - 1]) {
        throw bad_date("Invalid day for the given month and year.");
    }
}

bool Date::isValid() const {
    try 
    {
        validate();
    } catch (const bad_date& e) {
        return false;
    } catch (...) {
        throw;
    }
    return true;
}


// Egy véletlen dátum generálása a megadott intervallumban (egyenlőség is megengedett)
Date Date::randomDate(const Date &start, const Date &end) {
    #ifdef DEBUG
    std::vector<std::string> dates(MAX_TRY_RANDOM);
#endif

    for (int i = 0; i < MAX_TRY_RANDOM; ++i) 
    {
        // sajnos muszáj foglalkozni az intervallum két végén lévő dátumokkal is
        // ezeken a helyeken nem lehet az összes hónap összes napját választani
        int year = start.getYear() + std::rand() % (end.getYear() - start.getYear() + 1);
        int startMonth = (start.getYear() == year ? start.getMonth() : 1);
        int endMonth = (end.getYear() == year ? end.getMonth() : 12);
        int month = startMonth + std::rand() % (endMonth - startMonth + 1);
        int startDay = (start.getYear() == year && start.getMonth() == month ? start.getDay() : 1);
        int endDay = (end.getYear() == year && end.getMonth() == month ? end.getDay() : 31);
        int day = startDay + std::rand() % (endDay - startDay + 1);
        
        Date date(year, month, day);
        if (date.isValid()) {
            return date;
        }
        
#ifdef DEBUG
        std::ostringstream oss;
        oss << date;
        dates.push_back(oss.str());
#endif
    }

#ifdef DEBUG
    std::cerr << "Failed to generate a valid random date. Tried the following dates: ";
    for (std::vector<std::string>::const_iterator it = dates.begin(); it != dates.end(); ++it) {
        std::cerr << *it << std::endl;
    }
    std::cerr << std::endl;
#endif

    throw terrible_random("Failed to generate a valid random date.");
}
