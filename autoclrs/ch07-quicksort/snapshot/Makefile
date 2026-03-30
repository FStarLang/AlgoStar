# Standalone Makefile for CLRS Chapter 7 Quicksort — C snapshot
#
# This builds the extracted + handwritten C code without needing
# F*, Pulse, or KaRaMeL installed.  Only a C11 compiler is required.
#
# Usage:
#   make            # build and run tests
#   make test       # same as above
#   make clean      # remove build artifacts

CC       ?= cc
CFLAGS   = -std=c11 -Wall -g -fwrapv \
           -D_BSD_SOURCE -D_DEFAULT_SOURCE \
           -Wno-unused-variable -Wno-unused-parameter \
           -Wno-parentheses

INCLUDES = -I krmllib -I .
EXTRA_CFLAGS = -include fstar_support.h

EXE = quicksort_test

# KaRaMeL-generated sources
KRML_SRCS = \
  CLRS_Ch07_Quicksort_Impl.c \
  CLRS_Ch07_Quicksort_ImplTest.c \
  CLRS_Ch07_Partition_Impl.c \
  CLRS_Ch07_Partition_ImplTest.c

# Handwritten + runtime sources
HAND_SRCS = \
  main.c \
  fstar_support.c \
  krmllib/prims.c

SRCS = $(HAND_SRCS) $(KRML_SRCS)

.PHONY: all test clean

all: test

$(EXE): $(SRCS)
	$(CC) $(CFLAGS) $(EXTRA_CFLAGS) $(INCLUDES) -o $@ $(SRCS)

test: $(EXE)
	./$(EXE)

clean:
	rm -f $(EXE)
