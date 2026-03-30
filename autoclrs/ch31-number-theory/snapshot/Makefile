# Standalone Makefile for CLRS Chapter 31 — Number Theory snapshot
#
# This snapshot is a self-contained C distribution extracted from
# verified F*/Pulse code via KaRaMeL.  No F*, Pulse, or KaRaMeL
# installation is required to build and run it.
#
# Usage:
#   make          # compile the test executable
#   make test     # compile and run tests
#   make clean    # remove build artifacts

CC       ?= cc
CFLAGS   ?= -std=c11 -Wall -g -fwrapv \
            -D_BSD_SOURCE -D_DEFAULT_SOURCE \
            -Wno-unused-variable -Wno-unused-parameter \
            -Wno-parentheses

EXE      = ch31_test

SOURCES  = main.c Ch31_NumberTheory.c
HEADERS  = Ch31_NumberTheory.h

.PHONY: all test clean

all: $(EXE)

$(EXE): $(SOURCES) $(HEADERS)
	$(CC) $(CFLAGS) -I . -o $@ $(SOURCES)

test: $(EXE)
	./$(EXE)

clean:
	rm -f $(EXE)
