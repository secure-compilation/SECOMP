SOURCES := $(filter-out $(wildcard *.parsed.c), $(wildcard *.c))
OBJECTS := $(SOURCES:.c=.s)
PARSED_OBJECTS := $(SOURCES:.c=.parsed.c)

all: $(OBJECTS)

%.s %.parsed.c: %.c
	../../ccomp $*.c -L../../runtime -dasm -dparse

clean:
	rm -f $(OBJECTS) $(PARSED_OBJECTS)
