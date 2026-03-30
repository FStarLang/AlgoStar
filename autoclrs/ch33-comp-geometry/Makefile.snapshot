# Standalone Makefile for the CLRS Ch33 Computational Geometry snapshot.
#
# This directory is self-contained: all generated C/H files and the
# krmllib headers needed to compile them are included.
#
# Usage:
#   make          # build and run the tests
#   make build    # build only
#   make run      # run only (builds first)
#   make clean    # remove build artifacts

CC       ?= cc
CFLAGS   = -std=c11 -Wall -g -fwrapv \
           -D_BSD_SOURCE -D_DEFAULT_SOURCE \
           -Wno-unused-variable -Wno-unused-parameter \
           -Wno-parentheses -Wextra -Wno-unused-but-set-variable \
           -ffunction-sections -fdata-sections
LDFLAGS  = -Wl,--gc-sections

BUNDLE   = CLRS_Ch33_Segments_ImplTest_CLRS_Ch33_GrahamScan_ImplTest_CLRS_Ch33_JarvisMarch_ImplTest
EXE      = ch33_test

SRCS     = main.c $(BUNDLE).c prims.c
INCLUDES = -I .

.PHONY: all build run clean

all: run

build: $(EXE)

$(EXE): $(SRCS) $(BUNDLE).h
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $(SRCS) $(LDFLAGS)

run: $(EXE)
	./$(EXE)

clean:
	rm -f $(EXE)
