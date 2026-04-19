include ../config.mk
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID       = ch13
KRML_INPUT_FILES = $(OUTPUT_DIR)/CLRS_Ch13_RBTree_Main.krml \
                   $(OUTPUT_DIR)/CLRS_Ch13_RBTree_ImplTest.krml \
                   $(OUTPUT_DIR)/CLRS_Ch13_RBTree_Impl.krml \
                   $(OUTPUT_DIR)/CLRS_Ch13_RBTree_Spec.krml \
                   $(OUTPUT_DIR)/FStar_Pervasives_Native.krml \
                   $(OUTPUT_DIR)/FStar_Pervasives.krml
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch13.RBTree.Main=CLRS.Ch13.RBTree.*' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_EXTRA_FLAGS  =
# Warning -15: expected — Impl uses F*'s unbounded `int` for keys, which
# KaRaMeL maps to krml_checked_int_t (int32_t with overflow checks).
# The compat.h header is included to provide this fallback.
# Warning -2: standard (unused variables from ghost erasure).
KRML_WARN_FLAGS   = -warn-error -2-15
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch13_RBTree_Main.c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(KRML_HOME)/krmllib/c/fstar_int32.c
TEST_MAIN         = test_main.c
TEST_EXE_NAME     = test_rbtree

include ../autoclrs.test.mk

# ── Snapshot target ─────────────────────────────────────────────────
# Build a self-contained snapshot/ directory with all extracted C/H
# files and the KaRaMeL runtime needed to compile without F*/KaRaMeL.

SNAPSHOT_DIR = snapshot

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES)
	@echo "  [SNAPSHOT] Populating $(SNAPSHOT_DIR)/"
	@mkdir -p $(SNAPSHOT_DIR)/internal $(SNAPSHOT_DIR)/krml/internal
	@# ── Generated C and headers ──
	cp $(EXTRACT_DIR)/CLRS_Ch13_RBTree_Main.c          $(SNAPSHOT_DIR)/
	cp $(EXTRACT_DIR)/CLRS_Ch13_RBTree_Main.h          $(SNAPSHOT_DIR)/
	cp $(EXTRACT_DIR)/internal/CLRS_Ch13_RBTree_Main.h  $(SNAPSHOT_DIR)/internal/
	cp $(EXTRACT_DIR)/internal/FStar_Pulse_PulseCore_Prims.h $(SNAPSHOT_DIR)/internal/
	@# ── KaRaMeL runtime C sources ──
	cp $(KRML_HOME)/krmllib/dist/generic/prims.c        $(SNAPSHOT_DIR)/
	cp $(KRML_HOME)/krmllib/c/fstar_int32.c             $(SNAPSHOT_DIR)/
	@# ── KaRaMeL runtime headers ──
	cp $(KRML_HOME)/include/krmllib.h                   $(SNAPSHOT_DIR)/
	cp $(KRML_HOME)/include/krml/fstar_int.h            $(SNAPSHOT_DIR)/krml/
	cp $(KRML_HOME)/include/krml/lowstar_endianness.h   $(SNAPSHOT_DIR)/krml/
	cp $(KRML_HOME)/include/krml/internal/builtin.h     $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_HOME)/include/krml/internal/callconv.h    $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_HOME)/include/krml/internal/compat.h      $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_HOME)/include/krml/internal/debug.h       $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_HOME)/include/krml/internal/target.h      $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_HOME)/include/krml/internal/types.h       $(SNAPSHOT_DIR)/krml/internal/
	@# ── KaRaMeL dist headers (minimal + generic) ──
	cp $(KRML_HOME)/krmllib/dist/minimal/FStar_UInt128.h        $(SNAPSHOT_DIR)/
	cp $(KRML_HOME)/krmllib/dist/minimal/fstar_uint128_gcc64.h  $(SNAPSHOT_DIR)/
	cp $(KRML_HOME)/krmllib/dist/minimal/FStar_UInt_8_16_32_64.h $(SNAPSHOT_DIR)/
	cp $(KRML_HOME)/krmllib/dist/minimal/LowStar_Endianness.h  $(SNAPSHOT_DIR)/
	cp $(KRML_HOME)/krmllib/dist/generic/Prims.h                $(SNAPSHOT_DIR)/
	cp $(KRML_HOME)/krmllib/dist/generic/FStar_Int32.h          $(SNAPSHOT_DIR)/
	@echo "  [SNAPSHOT] Done — run 'make -C $(SNAPSHOT_DIR) test' to build and test"
