# Compiler settings - default to g++
CXX = g++
CXXFLAGS = -Wall -std=c++17
DEBUGFLAGS = -g -DDEBUG
OPTFLAGS = -O3

COMMON_OBJECTS = date.o

GENERATOR_OBJECTS = $(COMMON_OBJECTS) generator.o
GENERATOR_EXEC = generator

MAIN_OBJECTS = $(COMMON_OBJECTS) consumer.o main.o
MAIN_EXEC = app

# Check for target postfix
ifneq (,$(findstring -llvm,$(MAKECMDGOALS)))
  CXX = clang++
endif

# Default target
all: CXXFLAGS += $(DEBUGFLAGS)
all: $(GENERATOR_EXEC) $(MAIN_EXEC)

# LLVM version of the default target
all-llvm: all

# Production target with maximum optimization
prod: CXXFLAGS += $(OPTFLAGS)
prod: $(GENERATOR_EXEC) $(MAIN_EXEC)

# LLVM version of the production target
prod-llvm: prod

$(GENERATOR_EXEC): $(GENERATOR_OBJECTS)
	$(CXX) $(CXXFLAGS) -o $@ $^

$(MAIN_EXEC): $(MAIN_OBJECTS)
	$(CXX) $(CXXFLAGS) -o $@ $^

# Rule to create object files
%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -f $(GENERATOR_OBJECTS) $(MAIN_OBJECTS) $(GENERATOR_EXEC) $(MAIN_EXEC)

run: prod
	./$(GENERATOR_EXEC) 500 10000 dates.txt
	./$(MAIN_EXEC) dates.txt
