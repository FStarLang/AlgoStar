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
KRML_EXTRA_INPUTS = $(wildcard $(KRML_HOME)/krmllib/.extract/*.krml)
EXTRACT_C_FILES   = $(OUTPUT_DIR)/ImplTest.c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c
CC_EXTRA_FLAGS    = -Wno-unused-but-set-variable
CC_EXTRA_INCLUDES = -I $(OUTPUT_DIR)/internal
TEST_EXE_NAME     = test_counting_sort

include ../autoclrs.test.mk

# ── Snapshot target ─────────────────────────────────────────────────
# Extracts verified C code into a self-contained snapshot/ directory
# that can be built and tested without F*, Pulse, or KaRaMeL.
SNAPSHOT_DIR = snapshot

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES)
	@echo "  SNAPSHOT       $(CHAPTER_ID)"
	@mkdir -p $(SNAPSHOT_DIR)/include $(SNAPSHOT_DIR)/dist/minimal \
	          $(SNAPSHOT_DIR)/dist/generic $(SNAPSHOT_DIR)/internal
	@# Generated files (F* + KaRaMeL)
	@cp $(EXTRACT_DIR)/ImplTest.c $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/ImplTest.h $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/internal/*.h $(SNAPSHOT_DIR)/internal/
	@# KaRaMeL runtime headers
	@cp -r $(KRML_HOME)/include/* $(SNAPSHOT_DIR)/include/
	@# KaRaMeL minimal distribution headers
	@cp $(KRML_HOME)/krmllib/dist/minimal/*.h $(SNAPSHOT_DIR)/dist/minimal/
	@# KaRaMeL generic runtime C sources
	@cp $(KRML_HOME)/krmllib/dist/generic/Prims.h      $(SNAPSHOT_DIR)/dist/generic/
	@cp $(KRML_HOME)/krmllib/dist/generic/prims.c       $(SNAPSHOT_DIR)/dist/generic/
	@cp $(KRML_HOME)/krmllib/dist/generic/FStar_Int32.h $(SNAPSHOT_DIR)/dist/generic/
	@cp $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c $(SNAPSHOT_DIR)/dist/generic/
	@echo "  Snapshot ready in $(SNAPSHOT_DIR)/"
