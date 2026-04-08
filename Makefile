# Top-level Makefile for CLRS Pulse implementations
#
# Usage:
#   make            # verify all chapters (parallel-safe with -j)
#   make verify     # same as 'make'
#   make clean      # clean all build artifacts
#   make -j8        # parallel build across chapters
#
# Prerequisites:
#   ./setup.sh binary   (install pre-built F* binary — fast)
#   OR
#   ./setup.sh          (build F* from source — requires OCaml)

.PHONY: all verify clean

all verify:
	$(MAKE) -C autoclrs $@

clean:
	$(MAKE) -C autoclrs $@
