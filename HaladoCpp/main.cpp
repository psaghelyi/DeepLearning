#include <iostream>
#include <string>
#include <stdexcept>
#include <ctime>

#include "date.hpp"

int main () {
    try {
        Date date = Date::create(1990, 11, 30); // Example of a valid date
        std::cout << date.getYear() << "-" << date.getMonth() << "-" << date.getDay() << std::endl;
    } catch (const bad_date& e) {
        std::cerr << "Exception caught: " << e.what() << std::endl;
    }
    return 0;
}
