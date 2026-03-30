# ── Standalone Makefile for CLRS Ch12 BST snapshot ──────────────────
#
# This directory is a self-contained C snapshot of the verified
# F*/Pulse BST implementation.  No F*, Pulse, or KaRaMeL installation
# is required — only a C11 compiler.
#
# Usage:
#   make          # build the test executable
#   make run      # build and run the tests
#   make clean    # remove build artefacts

CC       ?= cc
CFLAGS   ?= -std=c11 -Wall -g -fwrapv \
            -D_BSD_SOURCE -D_DEFAULT_SOURCE \
            -Wno-unused-variable -Wno-unused-parameter \
            -Wno-parentheses

EXE      = bst_test

# All C sources: handwritten driver + generated modules + krmllib support
SRCS = main.c \
       CLRS_Ch12_BST_TestMain.c \
       CLRS_Ch12_BSTArray_TestMain.c \
       krmllib/c/prims.c \
       krmllib/c/fstar_int32.c

# Include paths — mirrors the KaRaMeL toolchain layout
INCLUDES = -I krmllib/include \
           -I krmllib/dist/minimal \
           -I krmllib/dist/generic \
           -I .

.PHONY: all run clean

all: $(EXE)

$(EXE): $(SRCS)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $(SRCS)

run: $(EXE)
	./$(EXE)

clean:
	rm -f $(EXE)
