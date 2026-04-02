PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
STAGE3     ?= 1

include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch35
EXTRACT_DIR       = $(OUTPUT_DIR)/c_extract
KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch35_VertexCover_ImplTest.krml \
                    $(OUTPUT_DIR)/CLRS_Ch35_VertexCover_Impl.krml
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch35.VertexCover.ImplTest+CLRS.Ch35.VertexCover.Impl=*[rename=VertexCoverTest]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,CLRS.Ch35.VertexCover.Spec,CLRS.Ch35.VertexCover.Lemmas,CLRS.Ch35.VertexCover.Complexity'
KRML_EXTRA_FLAGS  = -header=$(PULSE_ROOT)/mk/krmlheader
KRML_EXTRA_INPUTS = $(wildcard $(KRML_HOME)/krmllib/.extract/*.krml)
EXTRACT_C_FILES   = $(EXTRACT_DIR)/VertexCoverTest.c
TEST_EXE_NAME     = test_vertex_cover

include ../autoclrs.test.mk

# ── Snapshot target ─────────────────────────────────────────────────
# Copies extracted .c/.h and required krmllib headers into snapshot/
# so that the snapshot can be built standalone (no F*/Pulse/KaRaMeL).

SNAPSHOT_DIR      = snapshot
KRML_INCLUDE_DIR  = $(KRML_HOME)/include
KRML_GENERIC_DIR  = $(KRML_HOME)/krmllib/dist/generic

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES)
	@echo "  [SNAPSHOT] Updating $(SNAPSHOT_DIR)/"
	@mkdir -p $(SNAPSHOT_DIR)/krml/internal $(SNAPSHOT_DIR)/krmllib
	cp $(EXTRACT_DIR)/VertexCoverTest.c $(SNAPSHOT_DIR)/
	cp $(EXTRACT_DIR)/VertexCoverTest.h $(SNAPSHOT_DIR)/
	cp $(KRML_INCLUDE_DIR)/krmllib.h $(SNAPSHOT_DIR)/
	cp $(KRML_INCLUDE_DIR)/krml/internal/builtin.h $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_INCLUDE_DIR)/krml/internal/callconv.h $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_INCLUDE_DIR)/krml/internal/compat.h $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_INCLUDE_DIR)/krml/internal/debug.h $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_INCLUDE_DIR)/krml/internal/target.h $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_INCLUDE_DIR)/krml/internal/types.h $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_INCLUDE_DIR)/krml/fstar_int.h $(SNAPSHOT_DIR)/krml/
	cp $(KRML_INCLUDE_DIR)/krml/lowstar_endianness.h $(SNAPSHOT_DIR)/krml/
	cp $(KRML_GENERIC_DIR)/fstar_uint128_gcc64.h $(SNAPSHOT_DIR)/krmllib/
	cp $(KRML_GENERIC_DIR)/fstar_uint128_msvc.h $(SNAPSHOT_DIR)/krmllib/
	cp $(KRML_GENERIC_DIR)/fstar_uint128_struct_endianness.h $(SNAPSHOT_DIR)/krmllib/
	cp $(KRML_GENERIC_DIR)/FStar_UInt128.h $(SNAPSHOT_DIR)/krmllib/
	cp $(KRML_GENERIC_DIR)/FStar_UInt128_Verified.h $(SNAPSHOT_DIR)/krmllib/
	cp $(KRML_GENERIC_DIR)/FStar_UInt_8_16_32_64.h $(SNAPSHOT_DIR)/krmllib/
	cp $(KRML_GENERIC_DIR)/LowStar_Endianness.h $(SNAPSHOT_DIR)/krmllib/
	@echo "  [SNAPSHOT] Done. Build with: cd $(SNAPSHOT_DIR) && make"
