INCLUDES= -I ./rilib/ -I ./include/ -I /usr/local/Cellar/boost/1.67.0_1/include/
CC=g++
CFLAGS=-c -O3 -std=c++11

SOURCES= ri3.cpp
OBJECTS=$(SOURCES:.cpp=.o)
EXECUTABLE=ri36


all:	$(SOURCES) $(EXECUTABLE)

$(EXECUTABLE): $(OBJECTS)
	$(CC) $(OBJECTS) -o $@

.cpp.o:
	$(CC) $(CFLAGS) $< $(INCLUDES) -o $@  
