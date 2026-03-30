# ============================================================================
# HANDWRITTEN FILE
#
# Standalone Makefile for the CLRS Chapter 23 MST snapshot.
# This directory is self-contained: all KaRaMeL runtime headers are bundled
# so that the code can be built without the full F*/KaRaMeL toolchain.
#
# Usage:
#   make          # build and run tests
#   make build    # build only
#   make run      # run the test executable
#   make clean    # remove build artifacts
# ============================================================================

CC       ?= cc
CFLAGS   := -std=c11 -Wall -g -fwrapv \
            -D_BSD_SOURCE -D_DEFAULT_SOURCE \
            -Wno-unused-variable -Wno-unused-parameter \
            -Wno-parentheses
INCLUDES := -I . -I krmllib

SOURCES  := main.c Ch23_MST.c prims.c fstar_support.c
TARGET   := mst_test

.PHONY: all build run clean

all: run

build: $(TARGET)

$(TARGET): $(SOURCES)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $(SOURCES)

run: $(TARGET)
	./$(TARGET)

clean:
	rm -f $(TARGET)
