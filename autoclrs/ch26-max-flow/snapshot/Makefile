# Makefile for CLRS Ch26 Max Flow — standalone C snapshot
#
# This snapshot is self-contained: it includes KaRaMeL-extracted C code,
# a minimal vendored subset of the KaRaMeL runtime (krmllib/), and a
# handwritten test driver. No F*, Pulse, or KaRaMeL installation is needed.
#
# Usage:
#   make          # build the test executable
#   make run      # build and run all tests
#   make clean    # remove build artifacts

CC       ?= gcc
CFLAGS   := -std=c11 -Wall -g -fwrapv \
            -D_BSD_SOURCE -D_DEFAULT_SOURCE \
            -Wno-unused-variable -Wno-unused-parameter \
            -Wno-parentheses
INCLUDES := -I . -I krmllib
EXTRA_INCLUDES := -include clrs_ch26_compat.h

EXE      := test_max_flow

SRCS     := test_main.c \
            CLRS_Ch26_MaxFlow_ImplTest.c \
            krmllib/prims.c

.PHONY: all run clean

all: $(EXE)

$(EXE): $(SRCS)
	$(CC) $(CFLAGS) $(INCLUDES) $(EXTRA_INCLUDES) -o $@ $(SRCS)

run: $(EXE)
	./$(EXE)

clean:
	rm -f $(EXE)
