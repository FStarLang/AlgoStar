# Makefile for the ch08 counting sort snapshot
#
# This builds and runs the verified counting sort extracted from F*/Pulse
# via KaRaMeL.  No F*, Pulse, or KaRaMeL installation is required —
# all generated C and the KaRaMeL runtime headers are included.
#
# Usage:
#   make            # build and run tests
#   make build      # build only
#   make test       # build and run
#   make clean      # remove build artifacts

CC      ?= cc
CFLAGS  ?= -std=c11 -Wall -g -fwrapv \
           -D_BSD_SOURCE -D_DEFAULT_SOURCE \
           -Wno-unused-variable -Wno-unused-parameter \
           -Wno-parentheses -Wno-unused-but-set-variable

INCLUDES = -I . -I include -I dist/minimal -I dist/generic -I internal

EXE = test_counting_sort

# Sources
GENERATED_C = ImplTest.c dist/generic/prims.c dist/generic/fstar_int32.c
HANDWRITTEN_C = main.c
ALL_C = $(HANDWRITTEN_C) $(GENERATED_C)

.PHONY: all build test clean

all: test

build: $(EXE)

$(EXE): $(ALL_C)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $^

test: $(EXE)
	./$(EXE)

clean:
	rm -f $(EXE)
