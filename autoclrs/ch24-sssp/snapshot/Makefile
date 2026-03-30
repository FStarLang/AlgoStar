# Standalone Makefile for the Ch24 SSSP snapshot
#
# This builds and runs the extracted C tests without requiring
# F*, Pulse, or KaRaMeL.  All generated and runtime files are
# included in this directory.
#
# Usage:
#   make          # build and run tests
#   make build    # build only
#   make test     # run tests
#   make clean    # remove build artifacts

CC       ?= cc
CFLAGS   := -std=c11 -Wall -g -fwrapv \
            -D_BSD_SOURCE -D_DEFAULT_SOURCE \
            -Wno-unused-variable -Wno-unused-parameter \
            -Wno-parentheses \
            -ffunction-sections -fdata-sections
LDFLAGS  := -Wl,--gc-sections

INCLUDES := -I krml_include -I .
EXE      := test_ch24

# Source files
C_SRCS := main.c Ch24_SSSP.c krmlinit.c prims.c fstar_support.c

.PHONY: all build test clean

all: test

build: $(EXE)

$(EXE): $(C_SRCS) $(wildcard *.h internal/*.h krml_include/krml/internal/*.h)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $(C_SRCS) $(LDFLAGS)

test: $(EXE)
	@./$(EXE)

clean:
	rm -f $(EXE)
