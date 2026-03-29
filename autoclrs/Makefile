# autoclrs/Makefile — Build all CLRS chapter directories
#
# Usage (from repo root):
#   make            # verify all chapters
#   make -j8        # parallel build

PULSE_ROOT ?= ../FStar/pulse
STAGE3     ?= 1
export STAGE3
ifndef FSTAR_EXE
FSTAR_EXE  := $(CURDIR)/../FStar/out/bin/fstar.exe
endif
export FSTAR_EXE

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
