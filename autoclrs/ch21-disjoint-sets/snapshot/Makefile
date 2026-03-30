# Makefile for CLRS Ch21 Union-Find snapshot
#
# This directory contains a self-contained C snapshot of the verified
# F*/Pulse union-find implementation, extracted via KaRaMeL.
#
# Usage:
#   make          # build the test executable
#   make test     # build and run
#   make clean    # remove build artifacts

CC      ?= gcc
CFLAGS   = -std=c11 -Wall -g -fwrapv \
           -D_BSD_SOURCE -D_DEFAULT_SOURCE \
           -Wno-unused-variable -Wno-unused-parameter -Wno-parentheses

SOURCES  = main.c CLRS_Ch21_UnionFind_ImplTest.c
TARGET   = test_union_find

all: $(TARGET)

$(TARGET): $(SOURCES) CLRS_Ch21_UnionFind_ImplTest.h
	$(CC) $(CFLAGS) -I . -o $@ $(SOURCES)

.PHONY: test clean

test: $(TARGET)
	./$(TARGET)

clean:
	rm -f $(TARGET)
