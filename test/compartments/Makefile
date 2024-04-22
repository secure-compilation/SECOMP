SOURCES := $(wildcard *.c)

all: $(SOURCES:.c=.s)

%.s: %.c
	../../ccomp $*.c -L../../runtime -dasm -dparse
