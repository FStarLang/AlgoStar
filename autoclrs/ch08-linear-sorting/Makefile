PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
KRML_EXE   ?= $(KRML_HOME)/krml
STAGE3     ?= 1
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch08

KRML_MODULES = CLRS_Ch08_CountingSort_ImplTest CLRS_Ch08_CountingSort_Impl

KRML_INPUT_FILES  = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(KRML_MODULES))
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch08.CountingSort.ImplTest+CLRS.Ch08.CountingSort.Impl=CLRS.Ch08.CountingSort.ImplTest,CLRS.Ch08.CountingSort.Impl[rename=ImplTest]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,CLRS.Ch08.CountingSort.Spec,CLRS.Ch08.CountingSort.Lemmas,CLRS.Ch08.CountingSort.StableLemmas,CLRS.Ch08.CountingSort.DigitSortLemmas,CLRS.Ch08.RadixSort.*'
KRML_EXTRA_FLAGS  = -add-early-include '"fstar_sizet_shim.h"'
KRML_EXTRA_INPUTS = $(KRML_HOME)/krmllib/.extract/*.krml
EXTRACT_C_FILES   = $(OUTPUT_DIR)/ImplTest.c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c
CC_EXTRA_FLAGS    = -Wno-unused-but-set-variable
CC_EXTRA_INCLUDES = -I $(OUTPUT_DIR)/internal
TEST_EXE_NAME     = test_counting_sort

include ../autoclrs.test.mk
