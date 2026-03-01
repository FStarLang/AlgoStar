# Top-level Makefile for CLRS Pulse implementations
# Builds all chapter directories incrementally via the Pulse test framework.
#
# Usage:
#   make            # verify all chapters (parallel-safe with -j)
#   make verify     # same as 'make'
#   make clean      # clean all build artifacts
#   make -j8        # parallel build across chapters
#   make extract    # extract all modules to C via karamel
#   make test       # extract, compile, and run C tests
#
# Each chapter has its own .depend for incremental builds.
# Chapters are independent — no cross-chapter dependencies.

PULSE_ROOT ?= ../pulse
KRML_HOME  ?= ../karamel

SUBDIRS += ch02-getting-started
SUBDIRS += ch04-divide-conquer
SUBDIRS += ch06-heapsort
SUBDIRS += ch07-quicksort
SUBDIRS += ch08-linear-sorting
SUBDIRS += ch09-order-statistics
SUBDIRS += ch10-elementary-ds
SUBDIRS += ch11-hash-tables
SUBDIRS += ch12-bst
SUBDIRS += ch15-dynamic-programming
SUBDIRS += ch16-greedy
SUBDIRS += ch21-disjoint-sets
SUBDIRS += ch22-elementary-graph
SUBDIRS += ch23-mst
SUBDIRS += ch24-sssp
SUBDIRS += ch25-apsp
SUBDIRS += ch26-max-flow
SUBDIRS += ch31-number-theory
SUBDIRS += ch32-string-matching
SUBDIRS += ch33-comp-geometry
SUBDIRS += ch35-approximation

include $(PULSE_ROOT)/mk/test.mk

# ---- C Extraction and Testing ----

EXTRACTED_DIR = test/extracted
TEST_BIN      = test/run_tests
KRML_ABS      = $(abspath $(KRML_HOME))

CC_FLAGS = -I $(KRML_ABS)/include \
           -I $(KRML_ABS)/krmllib/dist/generic \
           -I $(KRML_ABS)/krmllib/dist/minimal \
           -I $(EXTRACTED_DIR) \
           -Wno-parentheses -Wno-unused-variable -Wno-implicit-function-declaration \
           -g -fwrapv -D_BSD_SOURCE -D_DEFAULT_SOURCE -std=c11

# Extract all Pulse modules to C
extract: verify
	PULSE_ROOT=$(abspath $(PULSE_ROOT)) KRML_HOME=$(KRML_ABS) ./test/extract.sh

# Compile the C test binary
$(TEST_BIN): extract test/main.c test/krmlinit.c
	cd $(EXTRACTED_DIR) && cc $(CC_FLAGS) -I . \
	    -o $(CURDIR)/$(TEST_BIN) \
	    $(CURDIR)/test/main.c \
	    $(CURDIR)/test/krmlinit.c \
	    $(CURDIR)/$(EXTRACTED_DIR)/CLRS_*.c \
	    $(KRML_ABS)/krmllib/dist/generic/prims.c \
	    $(KRML_ABS)/krmllib/dist/generic/fstar_int32.c

# Run the tests
test: $(TEST_BIN)
	./$(TEST_BIN)

# Clean extracted files and test binary
test-clean:
	rm -rf $(EXTRACTED_DIR) $(TEST_BIN)

.PHONY: extract test test-clean
