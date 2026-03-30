# Standalone Makefile for Ch32 String Matching snapshot
#
# This builds the verified C code extracted from F*/Pulse without
# requiring an F* or KaRaMeL installation.
#
# Usage:
#   make          # build and run tests
#   make build    # build only
#   make test     # build and run
#   make clean    # remove build artifacts

CC      ?= cc
CFLAGS  = -std=c11 -Wall -g -fwrapv \
          -D_BSD_SOURCE -D_DEFAULT_SOURCE \
          -Wno-unused-variable -Wno-unused-parameter \
          -Wno-parentheses -Wno-unused-function

INCLUDES = -I . -I krmllib -I krmllib/dist/minimal -I krmllib/dist/generic

SOURCES = main.c \
          Ch32_StringMatch.c \
          krmllib/dist/generic/prims.c \
          krmllib/dist/generic/fstar_int32.c

TARGET = ch32_test

.PHONY: all build test clean

all: test

build: $(TARGET)

$(TARGET): $(SOURCES) Ch32_StringMatch.h ch32_shims.h
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $(SOURCES)

test: $(TARGET)
	./$(TARGET)

clean:
	rm -f $(TARGET)
