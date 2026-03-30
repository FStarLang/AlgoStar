# Makefile for Ch22 Elementary Graph Algorithms — standalone C snapshot
#
# This directory contains a self-contained C snapshot extracted from the
# verified F*/Pulse implementation of CLRS Chapter 22 (BFS, DFS,
# Topological Sort).
#
# Generated C code was produced by F* + KaRaMeL from proved-correct
# Pulse source.  The KaRaMeL runtime headers are vendored in krmllib/.
#
# Usage:
#   make          # build and run the tests
#   make build    # compile only
#   make run      # run the test executable
#   make clean    # remove build artifacts

CC      ?= cc
CFLAGS  = -std=c11 -Wall -g -fwrapv \
          -D_BSD_SOURCE -D_DEFAULT_SOURCE \
          -Wno-unused-variable -Wno-unused-parameter \
          -Wno-parentheses

INCLUDES = \
  -I krmllib/include \
  -I krmllib/dist/minimal \
  -I krmllib/dist/generic \
  -I .

EXE = ch22_test

SOURCES = \
  main.c \
  CLRS_Ch22_ImplTestMain.c \
  fstar_support.c \
  krmllib/dist/generic/prims.c

.PHONY: all build run clean

all: run

build: $(EXE)

$(EXE): $(SOURCES)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $(SOURCES)

run: $(EXE)
	./$(EXE)

clean:
	rm -f $(EXE)
