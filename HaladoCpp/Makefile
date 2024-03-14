# Compiler settings
CXX = g++
CXXFLAGS = -Wall
DEBUGFLAGS = -g
OPTFLAGS = -O3

# Find all cpp files in the current directory
SOURCES = $(wildcard *.cpp)
# Replace .cpp extension with .o for object files
OBJECTS = $(SOURCES:.cpp=.o)

# Name of the executable
EXECUTABLE = app

# Default target
all: CXXFLAGS += $(DEBUGFLAGS)
all: $(EXECUTABLE)

# Production target with maximum optimization
prod: CXXFLAGS += $(OPTFLAGS)
prod: $(EXECUTABLE)

$(EXECUTABLE): $(OBJECTS)
	$(CXX) $(CXXFLAGS) -o $@ $^

# Rule to create object files
%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -f $(OBJECTS) $(EXECUTABLE)
