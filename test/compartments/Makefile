SOURCES := $(filter-out $(wildcard *.parsed.c), $(wildcard *.c))
OBJECTS := $(SOURCES:.c=.s)
PARSED_SOURCES := $(SOURCES:.c=.parsed.c)
PARSED_IMPORTS := $(SOURCES:.c=.parsed.imports)
EXECUTABLES := $(SOURCES:.c=.compcert)

all: $(OBJECTS)

%.compcert %.s %.s.intf %.parsed.c %.parsed.intf: %.c
	../../ccomp $*.c -L../../runtime -dasm -dparse -o $*.compcert

clean:
	rm -f $(OBJECTS) $(PARSED_SOURCES) $(PARSED_IMPORTS) $(EXECUTABLES) *.intf
