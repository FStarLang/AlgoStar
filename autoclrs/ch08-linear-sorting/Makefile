PULSE_ROOT ?= ../../pulse
KRML_HOME  ?= ../../krml/karamel
KRML_EXE   ?= $(KRML_HOME)/krml
include $(PULSE_ROOT)/mk/test.mk

# ============================================================================
# C extraction and test for CountingSort ImplTest
# ============================================================================

EXTRACT_DIR = _output

KRML_MODULES = CLRS_Ch08_CountingSort_ImplTest CLRS_Ch08_CountingSort_Impl

KRML_FILES = $(patsubst %,$(EXTRACT_DIR)/%.krml,$(KRML_MODULES))

KRML_BUNDLE = \
  -bundle 'CLRS.Ch08.CountingSort.ImplTest+CLRS.Ch08.CountingSort.Impl=CLRS.Ch08.CountingSort.ImplTest,CLRS.Ch08.CountingSort.Impl[rename=ImplTest]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,CLRS.Ch08.CountingSort.Spec,CLRS.Ch08.CountingSort.Lemmas,CLRS.Ch08.CountingSort.StableLemmas,CLRS.Ch08.CountingSort.DigitSortLemmas,CLRS.Ch08.RadixSort.*'

KRML_INCLUDE_DIRS = \
  -I$(KRML_HOME)/include \
  -I$(KRML_HOME)/krmllib/c \
  -I$(KRML_HOME)/krmllib/dist/generic \
  -I$(EXTRACT_DIR) \
  -I$(EXTRACT_DIR)/internal \
  -I.

.PHONY: extract-krml extract-c test-c

extract-krml: $(KRML_FILES)

extract-c: extract-krml
	$(KRML_EXE) \
	  -tmpdir $(EXTRACT_DIR) \
	  -skip-compilation \
	  -skip-makefiles \
	  -warn-error -2-9-11-15-17 \
	  $(KRML_BUNDLE) \
	  -add-early-include '"fstar_sizet_shim.h"' \
	  $(KRML_FILES) \
	  $(KRML_HOME)/krmllib/.extract/*.krml

test-c: extract-c
	$(CC) -std=c11 -Wall -Wno-unused-variable -Wno-unused-but-set-variable \
	  -D_BSD_SOURCE -D_DEFAULT_SOURCE \
	  $(KRML_INCLUDE_DIRS) \
	  main.c \
	  $(EXTRACT_DIR)/ImplTest.c \
	  $(KRML_HOME)/krmllib/dist/generic/prims.c \
	  $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c \
	  -o $(EXTRACT_DIR)/test_counting_sort
	@echo "=== Running Counting Sort tests ==="
	$(EXTRACT_DIR)/test_counting_sort

