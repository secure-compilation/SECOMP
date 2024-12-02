SOURCES := $(filter-out $(wildcard *.parsed.c), $(wildcard *.c))
OBJECTS := $(SOURCES:.c=.s)
PARSED_SOURCES := $(SOURCES:.c=.parsed.c)
PARSED_IMPORTS := $(SOURCES:.c=.parsed.imports)
EXECUTABLES := $(SOURCES:.c=.compcert)
INTERPS := $(SOURCES:.c=.interp)
INTERPASMS := $(SOURCES:.c=.interp-asm)

all: $(OBJECTS) $(INTERPS)

%.compcert %.s %.parsed.c %.parsed.intf: %.c
	../../ccomp $*.c -L../../runtime -dparse -dasm -v -static -o $*.compcert

%.interp %.interp-asm: %.c
	echo "dummy" | ../../ccomp $*.c -interp &> $*.interp
	echo "dummy" | ../../ccomp $*.c -interp-asm &> $*.interp-asm
#	meld $*.interp $*.interp-asm

clean:
	rm -f $(OBJECTS) $(PARSED_SOURCES) $(PARSED_IMPORTS) $(EXECUTABLES) $(INTERPS) $(INTERPASMS) *.intf
