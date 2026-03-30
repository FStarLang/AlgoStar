# Standalone Makefile for the ch35 Vertex Cover snapshot
#
# This builds and runs the extracted C code without requiring
# F*, Pulse, or KaRaMeL to be installed.
#
# Usage:
#   make          # build and run
#   make build    # build only
#   make test     # build and run
#   make clean    # remove build artifacts

CC       ?= cc
CFLAGS   ?= -std=c11 -Wall -g -fwrapv \
            -D_BSD_SOURCE -D_DEFAULT_SOURCE \
            -Wno-unused-variable -Wno-unused-parameter \
            -Wno-parentheses

INCLUDES  = -I . -I krml/internal -I krmllib -I krml

EXE       = test_vertex_cover

SRCS      = main.c VertexCoverTest.c

.PHONY: all build test clean

all: test

build: $(EXE)

$(EXE): $(SRCS) VertexCoverTest.h
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $(SRCS)

test: $(EXE)
	@echo "--- Running vertex cover test ---"
	./$(EXE)

clean:
	rm -f $(EXE)
