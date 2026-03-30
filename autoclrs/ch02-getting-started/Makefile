PULSE_ROOT ?= ../../FStar/pulse
STAGE3 ?= 1
export STAGE3
KRML_HOME ?= ../../FStar/karamel
OTHERFLAGS += --include ../common
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID       = ch02
EXTRACT_DIR      = $(OUTPUT_DIR)/csrc

# Modules to extract to .krml (test.mk pattern rules handle the extraction)
KRML_MODULES = CLRS.Ch02.InsertionSort.ImplTest \
               CLRS.Ch02.InsertionSort.Impl \
               CLRS.Ch02.MergeSort.ImplTest \
               CLRS.Ch02.MergeSort.Impl

KRML_INPUT_FILES = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(KRML_MODULES)))

KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch02.InsertionSort.ImplTest+CLRS.Ch02.InsertionSort.Impl=CLRS.Ch02.InsertionSort.*,CLRS.Common.*[rename=InsertionSort]' \
  -bundle 'CLRS.Ch02.MergeSort.ImplTest+CLRS.Ch02.MergeSort.Impl=CLRS.Ch02.MergeSort.*[rename=MergeSort]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_EXTRA_INPUTS = $(wildcard $(KRML_HOME)/krmllib/.extract/*.krml)
EXTRACT_C_FILES   = $(EXTRACT_DIR)/InsertionSort.c $(EXTRACT_DIR)/MergeSort.c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/c/prims.c \
                    $(KRML_HOME)/krmllib/c/fstar_int32.c
TEST_MAIN         = test_main.c
TEST_EXE_NAME     = test_ch02

include ../autoclrs.test.mk
