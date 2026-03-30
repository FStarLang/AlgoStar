# Standalone Makefile for CLRS Ch11 Hash Table — verified C snapshot
#
# This directory contains C code extracted from formally verified F* + Pulse
# source via KaRaMeL.  It builds and runs without the F*/Pulse/KaRaMeL
# toolchain — only a C11 compiler is needed.
#
# Usage:
#   make          # build the test executable
#   make test     # build and run all tests
#   make clean    # remove build artifacts

CC     ?= cc
CFLAGS  = -std=c11 -Wall -g -fwrapv \
          -D_BSD_SOURCE -D_DEFAULT_SOURCE \
          -Wno-unused-variable -Wno-unused-parameter \
          -Wno-parentheses

INCLUDES = -I .

SOURCES = main.c \
          CLRS_Ch11_HashTable_ImplTest.c \
          fstar_support.c \
          prims.c

TARGET = ch11_test

all: $(TARGET)

$(TARGET): $(SOURCES) $(wildcard *.h) $(wildcard internal/*.h) $(wildcard krml/internal/*.h)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $(SOURCES)

test: $(TARGET)
	./$(TARGET)

clean:
	rm -f $(TARGET)

.PHONY: all test clean
