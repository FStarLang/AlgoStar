PULSE_ROOT ?= ../../pulse
OTHERFLAGS += --include ../common
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch07
EXTRACT_DIR       = _output/c

KRML_INPUT_FILES  = _output/CLRS_Ch07_Quicksort_ImplTest.krml \
                    _output/CLRS_Ch07_Quicksort_Impl.krml \
                    _output/CLRS_Ch07_Partition_Impl.krml
KRML_BUNDLE_FLAGS =
KRML_WARN_FLAGS   = -warn-error -2-15
KRML_EXTRA_FLAGS  = -library CLRS.Ch07.Partition.Impl
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch07_Quicksort_Impl.c \
                    $(EXTRACT_DIR)/CLRS_Ch07_Quicksort_ImplTest.c
EXTRA_C_SOURCES   = CLRS_Ch07_Partition_Impl.c fstar_support.c \
                    $(KRML_HOME)/krmllib/dist/generic/prims.c
TEST_EXE_NAME     = quicksort_test.exe

include ../autoclrs.test.mk
