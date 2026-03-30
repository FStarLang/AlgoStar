PULSE_ROOT ?= ../../FStar/pulse
STAGE3     ?= 1
KRML_HOME  ?= ../../FStar/karamel
export STAGE3
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────────
CHAPTER_ID       = ch06
KRML_INPUT_FILES = $(OUTPUT_DIR)/CLRS_Ch06_Heap_Impl.krml \
                   $(OUTPUT_DIR)/CLRS_Ch06_Heap_ImplTest.krml \
                   $(OUTPUT_DIR)/Pulse_Lib_BoundedIntegers.krml
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch06.Heap.ImplTest=CLRS.Ch06.Heap.*,Pulse.Lib.BoundedIntegers' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
EXTRACT_C_FILES  = $(EXTRACT_DIR)/CLRS_Ch06_Heap_ImplTest.c
EXTRA_C_SOURCES  = fstar_support.c \
                   $(KRML_HOME)/krmllib/dist/generic/prims.c
CC_EXTRA_FLAGS   = -O2
TEST_EXE_NAME    = test_heapsort

include ../autoclrs.test.mk
