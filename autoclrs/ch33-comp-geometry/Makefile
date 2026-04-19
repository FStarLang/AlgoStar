include ../config.mk
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch33
EXTRACT_DIR       = $(OUTPUT_DIR)/c

EXTRACT_KRML_MODULES = \
  CLRS_Ch33_Segments_Impl \
  CLRS_Ch33_Segments_ImplTest \
  CLRS_Ch33_GrahamScan_Impl \
  CLRS_Ch33_GrahamScan_ImplTest \
  CLRS_Ch33_JarvisMarch_Impl \
  CLRS_Ch33_JarvisMarch_ImplTest

KRML_INPUT_FILES  = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(EXTRACT_KRML_MODULES))
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch33.Segments.ImplTest+CLRS.Ch33.GrahamScan.ImplTest+CLRS.Ch33.JarvisMarch.ImplTest=CLRS.Ch33.*' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_EXTRA_INPUTS = $(wildcard $(KRML_HOME)/krmllib/.extract/*.krml)

BUNDLE_NAME       = CLRS_Ch33_Segments_ImplTest_CLRS_Ch33_GrahamScan_ImplTest_CLRS_Ch33_JarvisMarch_ImplTest
EXTRACT_C_FILES   = $(EXTRACT_DIR)/$(BUNDLE_NAME).c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c
EXTRA_LINK_LIBS   = -Wl,--gc-sections
CC_EXTRA_FLAGS    = -Wextra -Wno-unused-but-set-variable -ffunction-sections -fdata-sections

include ../autoclrs.test.mk

# ── Snapshot: self-contained C directory ─────────────────────────────
SNAPSHOT_DIR = snapshot

# krmllib headers needed by extracted code
KRML_INCLUDE_DIR = $(KRML_HOME)/include

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES) $(TEST_MAIN)
	$(call msg, "SNAPSHOT", "$(SNAPSHOT_DIR)")
	@rm -rf $(SNAPSHOT_DIR)
	@mkdir -p $(SNAPSHOT_DIR)/internal
	@# --- Generated C files ---
	cp $(EXTRACT_DIR)/$(BUNDLE_NAME).c $(SNAPSHOT_DIR)/
	cp $(EXTRACT_DIR)/$(BUNDLE_NAME).h $(SNAPSHOT_DIR)/
	cp $(EXTRACT_DIR)/internal/*.h     $(SNAPSHOT_DIR)/internal/
	@# --- krmllib runtime support ---
	cp $(KRML_HOME)/krmllib/dist/generic/prims.c      $(SNAPSHOT_DIR)/
	cp $(KRML_HOME)/krmllib/dist/generic/Prims.h       $(SNAPSHOT_DIR)/
	cp $(KRML_HOME)/krmllib/dist/generic/FStar_Int32.h $(SNAPSHOT_DIR)/
	@# Copy the krmllib include tree
	cp -r $(KRML_INCLUDE_DIR)/krmllib.h       $(SNAPSHOT_DIR)/
	cp -r $(KRML_INCLUDE_DIR)/krml            $(SNAPSHOT_DIR)/
	@# Copy minimal dist headers (uint128 support, referenced by types.h)
	cp $(KRML_HOME)/krmllib/dist/minimal/*.h  $(SNAPSHOT_DIR)/krml/internal/
	@# --- Handwritten test driver ---
	cp $(TEST_MAIN) $(SNAPSHOT_DIR)/main.c
	@# --- Standalone build Makefile ---
	cp Makefile.snapshot $(SNAPSHOT_DIR)/Makefile
	@echo "Snapshot created in $(SNAPSHOT_DIR)/"
