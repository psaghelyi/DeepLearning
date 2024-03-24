#ifndef CONSUMER_HPP
#define CONSUMER_HPP

#include "date.hpp"

int consumer(Date const &date);

typedef int (*ConsumerFunction)(Date const &date);
extern ConsumerFunction consumerFunction;

#endif