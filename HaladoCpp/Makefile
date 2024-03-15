# Compiler settings - default to g++
CXX = g++
CXXFLAGS = -Wall -std=c++17
DEBUGFLAGS = -g -DDEBUG
OPTFLAGS = -O3

# Find all cpp files in the current directory
SOURCES = $(wildcard *.cpp)
# Replace .cpp extension with .o for object files
OBJECTS = $(SOURCES:.cpp=.o)

# Name of the executable
EXECUTABLE = app

# Check for target postfix
ifneq (,$(findstring -llvm,$(MAKECMDGOALS)))
  CXX = clang++
endif

# Default target
all: CXXFLAGS += $(DEBUGFLAGS)
all: $(EXECUTABLE)

# LLVM version of the default target
all-llvm: all

# Production target with maximum optimization
prod: CXXFLAGS += $(OPTFLAGS)
prod: $(EXECUTABLE)

# LLVM version of the production target
prod-llvm: prod

$(EXECUTABLE): $(OBJECTS)
	$(CXX) $(CXXFLAGS) -o $@ $^

# Rule to create object files
%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -f $(OBJECTS) $(EXECUTABLE)
