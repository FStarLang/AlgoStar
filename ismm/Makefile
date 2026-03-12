# Makefile for ISMM: Verified Reference Counting for Deeply Immutable Data Structures
#
# Uses F* and Pulse from sibling submodules (../FStar, ../pulse).
# Follows the same conventions as autoclrs/ch*/Makefile.

PULSE_ROOT ?= ../pulse

ifndef FSTAR_EXE
FSTAR_EXE := $(CURDIR)/../FStar/bin/fstar.exe
endif
export FSTAR_EXE

include $(PULSE_ROOT)/mk/test.mk

# Include autoclrs common utilities (predicates, list lemmas, etc.)
OTHERFLAGS += --include ../autoclrs/common
