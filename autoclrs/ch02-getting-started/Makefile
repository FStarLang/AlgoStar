PULSE_ROOT ?= ../../pulse
OTHERFLAGS += --include ../common
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID       = ch02
CSRC_DIR         = $(OUTPUT_DIR)/csrc
EXTRACT_DIR      = $(CSRC_DIR)

# Explicit .krml extraction rules
ISORT_KRML = $(OUTPUT_DIR)/CLRS_Ch02_InsertionSort_Impl.krml
MSORT_KRML = $(OUTPUT_DIR)/CLRS_Ch02_MergeSort_Impl.krml

$(ISORT_KRML): _cache/CLRS.Ch02.InsertionSort.Impl.fst.checked
	$(call msg, "EXTRACT", "CLRS_Ch02_InsertionSort_Impl.krml")
	$(FSTAR) CLRS.Ch02.InsertionSort.Impl.fst --codegen krml --extract 'CLRS.Ch02.InsertionSort.Impl'

$(MSORT_KRML): _cache/CLRS.Ch02.MergeSort.Impl.fst.checked
	$(call msg, "EXTRACT", "CLRS_Ch02_MergeSort_Impl.krml")
	$(FSTAR) CLRS.Ch02.MergeSort.Impl.fst --codegen krml --extract 'CLRS.Ch02.MergeSort.Impl'

KRML_INPUT_FILES  = $(ISORT_KRML) $(MSORT_KRML)
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch02.InsertionSort.Impl=CLRS.Ch02.InsertionSort.*,CLRS.Common.*[rename=InsertionSort]' \
  -bundle 'CLRS.Ch02.MergeSort.Impl=CLRS.Ch02.MergeSort.*[rename=MergeSort]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_EXTRA_INPUTS = $(KRML_HOME)/krmllib/.extract/*.krml
EXTRACT_C_FILES   = $(CSRC_DIR)/InsertionSort.c $(CSRC_DIR)/MergeSort.c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/c/prims.c \
                    $(KRML_HOME)/krmllib/c/fstar_int32.c
TEST_MAIN         = test_main.c
TEST_EXE_NAME     = test_ch02

include ../autoclrs.test.mk
