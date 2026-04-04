PULSE_ROOT ?= ../../FStar/pulse
STAGE3     ?= 1
KRML_HOME  ?= ../../FStar/karamel
include $(PULSE_ROOT)/mk/test.mk

# ========== C extraction and test targets for ImplTest ==========
CHAPTER_ID       = ch26

KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_ImplTest.krml \
                    $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_Impl.krml
KRML_BUNDLE_FLAGS = -bundle CLRS.Ch26.MaxFlow.ImplTest=CLRS.Ch26.MaxFlow.*
KRML_WARN_FLAGS   = -warn-error -2-9-11-15-17
EXTRACT_C_FILES   = $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_ImplTest.c
EXTRA_LINK_LIBS   =
CC_EXTRA_INCLUDES = -include clrs_ch26_compat.h
TEST_MAIN         = test_main.c
TEST_EXE_NAME     = test_max_flow

include ../autoclrs.test.mk

# ========== Snapshot: self-contained C directory ==========
SNAPSHOT_DIR     = snapshot
SNAPSHOT_KRMLLIB = $(SNAPSHOT_DIR)/krmllib

# KaRaMeL headers needed by extracted code (vendored into snapshot)
KRML_INCLUDE     = $(KRML_HOME)/include
KRML_DIST_MIN    = $(KRML_HOME)/krmllib/dist/minimal

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES)
	$(call msg, "SNAPSHOT", "$(CHAPTER_ID)")
	@mkdir -p $(SNAPSHOT_DIR)/internal
	@mkdir -p $(SNAPSHOT_KRMLLIB)/krml/internal
	@# ── Generated files (from KaRaMeL extraction) ──
	cp $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_ImplTest.c $(SNAPSHOT_DIR)/
	cp $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_ImplTest.h $(SNAPSHOT_DIR)/
	cp $(OUTPUT_DIR)/internal/Prims.h             $(SNAPSHOT_DIR)/internal/
	@# ── Handwritten files ──
	cp test_main.c         $(SNAPSHOT_DIR)/test_main.c
	cp clrs_ch26_compat.h  $(SNAPSHOT_DIR)/clrs_ch26_compat.h
	@# ── Vendored KaRaMeL runtime headers ──
	cp $(KRML_INCLUDE)/krmllib.h                      $(SNAPSHOT_KRMLLIB)/
	cp $(KRML_INCLUDE)/krml/lowstar_endianness.h      $(SNAPSHOT_KRMLLIB)/krml/
	cp $(KRML_INCLUDE)/krml/fstar_int.h               $(SNAPSHOT_KRMLLIB)/krml/
	cp $(KRML_INCLUDE)/krml/internal/target.h         $(SNAPSHOT_KRMLLIB)/krml/internal/
	cp $(KRML_INCLUDE)/krml/internal/callconv.h       $(SNAPSHOT_KRMLLIB)/krml/internal/
	cp $(KRML_INCLUDE)/krml/internal/builtin.h        $(SNAPSHOT_KRMLLIB)/krml/internal/
	cp $(KRML_INCLUDE)/krml/internal/debug.h          $(SNAPSHOT_KRMLLIB)/krml/internal/
	cp $(KRML_INCLUDE)/krml/internal/types.h          $(SNAPSHOT_KRMLLIB)/krml/internal/
	cp $(KRML_INCLUDE)/krml/internal/compat.h         $(SNAPSHOT_KRMLLIB)/krml/internal/
	cp $(KRML_DIST_MIN)/FStar_UInt_8_16_32_64.h       $(SNAPSHOT_KRMLLIB)/
	cp $(KRML_DIST_MIN)/FStar_UInt128.h                $(SNAPSHOT_KRMLLIB)/
	cp $(KRML_DIST_MIN)/fstar_uint128_gcc64.h          $(SNAPSHOT_KRMLLIB)/
	cp $(KRML_DIST_MIN)/LowStar_Endianness.h          $(SNAPSHOT_KRMLLIB)/
	@echo "Snapshot ready in $(SNAPSHOT_DIR)/ — run 'make -C $(SNAPSHOT_DIR) run'"

