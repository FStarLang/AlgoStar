# Top-level Makefile for CLRS Pulse implementations
# Builds all chapter directories incrementally via the Pulse test framework.
#
# Usage:
#   make            # verify all chapters (parallel-safe with -j)
#   make verify     # same as 'make'
#   make clean      # clean all build artifacts
#   make -j8        # parallel build across chapters
#
# Each chapter has its own .depend for incremental builds.
# Chapters are independent — no cross-chapter dependencies.

PULSE_ROOT ?= ../pulse

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
SUBDIRS += ch28-matrix-ops
SUBDIRS += ch31-number-theory
SUBDIRS += ch32-string-matching
SUBDIRS += ch33-comp-geometry
SUBDIRS += ch35-approximation

include $(PULSE_ROOT)/mk/test.mk
