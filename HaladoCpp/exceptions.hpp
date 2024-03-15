#ifndef EXCEPTIONS_HPP
#define EXCEPTIONS_HPP

#include <stdexcept>


class bad_date : public std::runtime_error {
public:
    bad_date(const std::string& message) : std::runtime_error(message) {}
};

class terrible_random : public std::runtime_error {
public:
    terrible_random(const std::string& message) : std::runtime_error(message) {}
};

#endif
