include ../config.mk
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch25
EXTRACT_DIR       = _extract

KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_Impl.krml \
                    $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_NegCycleDetect.krml \
                    $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_ImplTest.krml \
                    $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_Spec.krml

KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch25.FloydWarshall.ImplTest+CLRS.Ch25.FloydWarshall.NegCycleDetect+CLRS.Ch25.FloydWarshall.Impl=CLRS.*,Prims,FStar.*,Pulse.*,PulseCore.*[rename=CLRS_Ch25_FloydWarshall]'

KRML_EXTRA_FLAGS  = \
  -no-prefix CLRS.Ch25.FloydWarshall.Impl \
  -no-prefix CLRS.Ch25.FloydWarshall.NegCycleDetect \
  -no-prefix CLRS.Ch25.FloydWarshall.ImplTest

EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch25_FloydWarshall.c
TEST_MAIN         = test_main.c
TEST_EXE_NAME     = test_ch25

EXTRA_C_SOURCES   = fstar_support.c \
                    $(KRML_HOME)/krmllib/dist/generic/prims.c

include ../autoclrs.test.mk

# ── Snapshot: self-contained C directory ──────────────────────────────
SNAPSHOT_DIR = snapshot

# krmllib support files needed for standalone compilation
KRML_INCLUDE_DIR = $(KRML_HOME)/include
KRML_MINIMAL_DIR = $(KRML_HOME)/krmllib/dist/minimal
KRML_GENERIC_DIR = $(KRML_HOME)/krmllib/dist/generic

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES)
	@echo "=== Building snapshot ==="
	@rm -rf $(SNAPSHOT_DIR)
	@mkdir -p $(SNAPSHOT_DIR)/include/krml/internal
	@mkdir -p $(SNAPSHOT_DIR)/dist/minimal
	@mkdir -p $(SNAPSHOT_DIR)/dist/generic
	@# Generated files from F* + krml
	@cp $(EXTRACT_DIR)/CLRS_Ch25_FloydWarshall.c $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch25_FloydWarshall.h $(SNAPSHOT_DIR)/
	@# Handwritten files
	@cp test_main.c $(SNAPSHOT_DIR)/
	@cp fstar_support.c $(SNAPSHOT_DIR)/
	@# krmllib headers from karamel/include
	@cp $(KRML_INCLUDE_DIR)/krmllib.h $(SNAPSHOT_DIR)/include/
	@cp -r $(KRML_INCLUDE_DIR)/krml/* $(SNAPSHOT_DIR)/include/krml/
	@# krmllib dist/minimal headers (uint128 support)
	@for f in FStar_UInt128.h FStar_UInt128_Verified.h \
	          fstar_uint128_gcc64.h fstar_uint128_msvc.h \
	          fstar_uint128_struct_endianness.h \
	          FStar_UInt_8_16_32_64.h LowStar_Endianness.h; do \
	    [ -f $(KRML_MINIMAL_DIR)/$$f ] && cp $(KRML_MINIMAL_DIR)/$$f $(SNAPSHOT_DIR)/dist/minimal/; \
	done; true
	@# krmllib dist/generic: Prims runtime
	@cp $(KRML_GENERIC_DIR)/prims.c   $(SNAPSHOT_DIR)/dist/generic/
	@cp $(KRML_GENERIC_DIR)/Prims.h   $(SNAPSHOT_DIR)/dist/generic/
	@cp $(KRML_GENERIC_DIR)/FStar_Int32.h $(SNAPSHOT_DIR)/dist/generic/
	@# Snapshot Makefile
	@cp snapshot.Makefile $(SNAPSHOT_DIR)/Makefile
	@echo "=== Snapshot ready in $(SNAPSHOT_DIR)/ ==="
	@echo "=== Building and testing snapshot ==="
	@$(MAKE) -C $(SNAPSHOT_DIR) test
