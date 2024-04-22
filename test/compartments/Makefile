SOURCES := $(filter-out $(wildcard *.parsed.c), $(wildcard *.c))
OBJECTS := $(SOURCES:.c=.s)
PARSED_SOURCES := $(SOURCES:.c=.parsed.c)
PARSED_IMPORTS := $(SOURCES:.c=.parsed.imports)

all: $(OBJECTS)

%.s %.parsed.c %.parsed.imports: %.c
	../../ccomp $*.c -L../../runtime -dasm -dparse -S

clean:
	rm -f $(OBJECTS) $(PARSED_SOURCES) $(PARSED_IMPORTS)
