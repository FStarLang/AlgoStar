PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID = ch11

# Step 1: Combined extraction to single .krml
$(OUTPUT_DIR)/CLRS_Ch11_HashTable_combined.krml: \
    _cache/CLRS.Ch11.HashTable.ImplTest.fst.checked \
    _cache/CLRS.Ch11.HashTable.Impl.fst.checked
	@mkdir -p $(OUTPUT_DIR)
	$(call msg, "EXTRACT", "combined.krml")
	$(FSTAR) \
	  CLRS.Ch11.HashTable.ImplTest.fst \
	  --codegen krml \
	  --extract_module CLRS.Ch11.HashTable.Impl \
	  --extract_module CLRS.Ch11.HashTable.ImplTest \
	  -o $@

KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch11_HashTable_combined.krml
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch11.HashTable.ImplTest=CLRS.Ch11.HashTable.Impl' \
  -bundle 'FStar.*,Pulse.*,Prims,PulseCore.*,LowStar.*'
KRML_WARN_FLAGS   = -warn-error -9-2-15
KRML_EXTRA_FLAGS  = \
  -add-include '"CLRS_Ch11_HashTable_Impl.h"' \
  -header $(PULSE_ROOT)/mk/krmlheader
EXTRACT_C_FILES   = $(OUTPUT_DIR)/CLRS_Ch11_HashTable_ImplTest.c
EXTRA_C_SOURCES   = CLRS_Ch11_HashTable_Impl.c

include ../autoclrs.test.mk

# Alias for backward compatibility
.PHONY: test
test: test-c
