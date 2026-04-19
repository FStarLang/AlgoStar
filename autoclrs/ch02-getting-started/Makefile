include ../config.mk
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

# ── Snapshot target ────────────────────────────────────────────────
# Produces a self-contained snapshot/ directory with all extracted C,
# vendored krmllib headers/runtime, and a standalone Makefile.

SNAPSHOT_DIR = snapshot

.PHONY: snapshot
snapshot: extract
	@echo "  [SNAPSHOT] $(CHAPTER_ID)"
	@rm -rf $(SNAPSHOT_DIR)
	@mkdir -p $(SNAPSHOT_DIR)/internal $(SNAPSHOT_DIR)/krmllib/c
	@# Generated C files
	@cp $(EXTRACT_DIR)/InsertionSort.c $(EXTRACT_DIR)/InsertionSort.h $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/MergeSort.c     $(EXTRACT_DIR)/MergeSort.h     $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/internal/MergeSort.h                            $(SNAPSHOT_DIR)/internal/
	@cp $(EXTRACT_DIR)/internal/FStar_Pulse_PulseCore_Prims.h          $(SNAPSHOT_DIR)/internal/
	@# Handwritten test driver
	@cp $(TEST_MAIN) $(SNAPSHOT_DIR)/
	@# Vendored krmllib: include tree (krmllib.h + krml/)
	@cp -r $(KRML_HOME)/include/* $(SNAPSHOT_DIR)/krmllib/
	@# Vendored krmllib: dist/minimal (uint128 headers)
	@cp $(KRML_HOME)/krmllib/dist/minimal/*.h $(SNAPSHOT_DIR)/krmllib/
	@# Vendored krmllib: dist/generic runtime headers
	@cp $(KRML_HOME)/krmllib/dist/generic/Prims.h       $(SNAPSHOT_DIR)/krmllib/
	@cp $(KRML_HOME)/krmllib/dist/generic/FStar_Int32.h  $(SNAPSHOT_DIR)/krmllib/
	@# Vendored krmllib: runtime C files
	@cp $(KRML_HOME)/krmllib/c/prims.c                   $(SNAPSHOT_DIR)/krmllib/c/
	@cp $(KRML_HOME)/krmllib/c/fstar_int32.c             $(SNAPSHOT_DIR)/krmllib/c/
	@# Standalone Makefile for the snapshot
	@cp snapshot.Makefile $(SNAPSHOT_DIR)/Makefile
	@echo "  Snapshot written to $(SNAPSHOT_DIR)/"
