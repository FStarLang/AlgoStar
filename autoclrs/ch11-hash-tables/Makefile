PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID = ch11

# Per-module .krml extraction (canonical pattern from test.mk)
KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch11_HashTable_Impl.krml \
                    $(OUTPUT_DIR)/CLRS_Ch11_HashTable_ImplTest.krml

# Bundle Impl into ImplTest (Impl functions become static)
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch11.HashTable.ImplTest=CLRS.Ch11.HashTable.Impl[rename=CLRS_Ch11_HashTable_ImplTest]' \
  -bundle 'FStar.*,Pulse.*,Prims,PulseCore.*,LowStar.*'
KRML_WARN_FLAGS   = -warn-error -2-9-15
KRML_EXTRA_FLAGS  = -add-include '"fstar_support.h"'
EXTRACT_C_FILES   = $(OUTPUT_DIR)/CLRS_Ch11_HashTable_ImplTest.c
EXTRA_C_SOURCES   = fstar_support.c \
                    $(KRML_HOME)/krmllib/dist/generic/prims.c

include ../autoclrs.test.mk

# Alias for backward compatibility
.PHONY: test
test: test-c
