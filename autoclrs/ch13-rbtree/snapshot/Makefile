# Standalone Makefile for the CLRS Ch.13 Red-Black Tree snapshot.
#
# This directory is self-contained: it includes all generated C code
# from F* + KaRaMeL extraction and the necessary KaRaMeL runtime
# headers/sources.  No external toolchain (F*, Pulse, KaRaMeL) is
# needed — only a C11 compiler.
#
# Usage:
#   make          # build the test executable
#   make test     # build and run the tests
#   make clean    # remove build artifacts

CC     ?= gcc
CFLAGS  = -std=c11 -Wall -g -fwrapv \
          -D_BSD_SOURCE -D_DEFAULT_SOURCE \
          -Wno-unused-variable -Wno-unused-parameter \
          -Wno-parentheses \
          -I.

SOURCES = test_main.c CLRS_Ch13_RBTree_Main.c prims.c fstar_int32.c
EXE     = test_rbtree

.PHONY: all test clean

all: $(EXE)

$(EXE): $(SOURCES)
	$(CC) $(CFLAGS) -o $@ $^

test: $(EXE)
	./$(EXE)

clean:
	rm -f $(EXE)
