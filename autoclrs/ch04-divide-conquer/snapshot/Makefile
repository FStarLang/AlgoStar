# Standalone Makefile for CLRS Chapter 4 snapshot
#
# This directory is a self-contained C snapshot of the verified
# CLRS Ch04 algorithms, extracted from F*/Pulse via KaRaMeL.
#
# Usage:
#   make          # build and run tests
#   make build    # compile only
#   make test     # build + run
#   make clean    # remove build artifacts
#
# Prerequisites: a C11 compiler (gcc or clang)

CC       ?= gcc
CFLAGS   := -std=c11 -Wall -g -fwrapv \
            -D_BSD_SOURCE -D_DEFAULT_SOURCE \
            -Wno-unused-variable -Wno-unused-parameter \
            -Wno-parentheses

INCLUDES := -I . -I krmllib -I krmllib/dist/generic -I krmllib/dist/minimal

BUNDLE_STEM = CLRS_Ch04_BinarySearch_ImplTest_CLRS_Ch04_MatrixMultiply_ImplTest_CLRS_Ch04_MaxSubarray_Kadane_ImplTest

SRCS = main.c \
       $(BUNDLE_STEM).c \
       krmllib/dist/generic/prims.c \
       krmllib/dist/generic/fstar_int32.c

EXE = ch04_test

.PHONY: all build test clean

all: test

build: $(EXE)

$(EXE): $(SRCS)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $^

test: $(EXE)
	@echo "=== Running CLRS Ch04 snapshot tests ==="
	./$(EXE)

clean:
	rm -f $(EXE)
