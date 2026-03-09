# Top-level Makefile for CLRS Pulse implementations
#
# Usage:
#   make            # verify all chapters (parallel-safe with -j)
#   make verify     # same as 'make'
#   make clean      # clean all build artifacts
#   make -j8        # parallel build across chapters
#
# Prerequisites:
#   1. git submodule update --init --recursive
#   2. ./setup.sh   (builds FStar and Pulse from submodules)

.PHONY: all verify clean

all verify:
	$(MAKE) -C autoclrs $@

clean:
	$(MAKE) -C autoclrs $@
