# snapshot/Makefile — Standalone build for Ch25 Floyd-Warshall extracted C code.
#
# This directory is self-contained: it includes the KaRaMeL-extracted C,
# handwritten test driver, and the subset of krmllib headers needed to
# compile without the F*/KaRaMeL toolchain.
#
# Usage:
#   make          # build the test executable
#   make test     # build and run the tests
#   make clean    # remove build artifacts

CC       ?= cc
CFLAGS   = -std=c11 -Wall -g -fwrapv \
           -D_BSD_SOURCE -D_DEFAULT_SOURCE \
           -Wno-unused-variable -Wno-unused-parameter \
           -Wno-parentheses

INCLUDES = -I include -I dist/minimal -I dist/generic -I .

EXE      = test_ch25

SOURCES  = test_main.c \
           CLRS_Ch25_FloydWarshall.c \
           dist/generic/prims.c \
           fstar_support.c

.PHONY: all test clean

all: $(EXE)

$(EXE): $(SOURCES)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $(SOURCES)

test: $(EXE)
	./$(EXE)

clean:
	rm -f $(EXE)
