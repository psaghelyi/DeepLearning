# Compiler settings - default to g++
CXX = g++
CXXFLAGS = -Wall -std=c++17
DEBUGFLAGS = -g -DDEBUG
OPTFLAGS = -O3

COMMON_OBJECTS = date.o

PRODUCER_OBJECTS = $(COMMON_OBJECTS) producer.o
PRODUCER_EXEC = producer

CONSUMER_OBJECTS = $(COMMON_OBJECTS) consumer.o
CONSUMER_EXEC = consumer

# Check for target postfix
ifneq (,$(findstring -llvm,$(MAKECMDGOALS)))
  CXX = clang++
endif

# Default target
all: CXXFLAGS += $(DEBUGFLAGS)
all: $(PRODUCER_EXEC) $(CONSUMER_EXEC)

# LLVM version of the default target
all-llvm: all

# Production target with maximum optimization
prod: CXXFLAGS += $(OPTFLAGS)
prod: $(PRODUCER_EXEC) $(CONSUMER_EXEC)

# LLVM version of the production target
prod-llvm: prod

$(PRODUCER_EXEC): $(PRODUCER_OBJECTS)
	$(CXX) $(CXXFLAGS) -o $@ $^

$(CONSUMER_EXEC): $(CONSUMER_OBJECTS)
	$(CXX) $(CXXFLAGS) -o $@ $^

# Rule to create object files
%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -f $(PRODUCER_OBJECTS) $(CONSUMER_OBJECTS) $(PRODUCER_EXEC) $(CONSUMER_EXEC)
