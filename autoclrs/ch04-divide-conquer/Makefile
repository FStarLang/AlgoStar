PULSE_ROOT ?= ../../FStar/pulse
STAGE3     ?= 1
export STAGE3
ifndef FSTAR_EXE
FSTAR_EXE  := $(realpath ../../FStar/out/bin/fstar.exe)
endif
export FSTAR_EXE

KRML_HOME  ?= ../../FStar/karamel
KRML_EXE   ?= $(KRML_HOME)/krml

include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ───────────────────────────────────────
CHAPTER_ID         = ch04

IMPL_MODULES = \
  CLRS.Ch04.BinarySearch.Impl \
  CLRS.Ch04.MatrixMultiply.Impl \
  CLRS.Ch04.MaxSubarray.Kadane

TEST_MODULES = \
  CLRS.Ch04.BinarySearch.ImplTest \
  CLRS.Ch04.MatrixMultiply.ImplTest \
  CLRS.Ch04.MaxSubarray.Kadane.ImplTest

ALL_EXTRACT_MODULES = $(IMPL_MODULES) $(TEST_MODULES)

BUNDLE_API = CLRS.Ch04.BinarySearch.ImplTest+CLRS.Ch04.MatrixMultiply.ImplTest+CLRS.Ch04.MaxSubarray.Kadane.ImplTest
BUNDLE_C_STEM = CLRS_Ch04_BinarySearch_ImplTest_CLRS_Ch04_MatrixMultiply_ImplTest_CLRS_Ch04_MaxSubarray_Kadane_ImplTest

# Per-module .krml extraction convenience (maps dotted names to underscored filenames)
$(OUTPUT_DIR)/%_krml_extracted: _cache/%.fst.checked
	$(call msg, "EXTRACT", $*)
	$(FSTAR) $< --codegen krml --extract_module $*
	@touch $@

define krml_rule
$(OUTPUT_DIR)/$(subst .,_,$(1)).krml: $(OUTPUT_DIR)/$(1)_krml_extracted
	@true
endef
$(foreach m,$(ALL_EXTRACT_MODULES),$(eval $(call krml_rule,$(m))))

KRML_INPUT_FILES  = $(foreach m,$(ALL_EXTRACT_MODULES),$(OUTPUT_DIR)/$(subst .,_,$(m)).krml)
KRML_BUNDLE_FLAGS = -bundle '$(BUNDLE_API)=CLRS.Ch04.*' \
                    -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_EXTRA_FLAGS  = -header=$(PULSE_ROOT)/mk/krmlheader
EXTRACT_C_FILES   = $(OUTPUT_DIR)/$(BUNDLE_C_STEM).c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c

include ../autoclrs.test.mk

# ── Snapshot target ──────────────────────────────────────────────────
# Produces a self-contained C directory in snapshot/ that can be built
# without F*, Pulse, or KaRaMeL.

SNAPSHOT_DIR = snapshot

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES)
	$(call msg, "SNAPSHOT", "$(CHAPTER_ID)")
	@# ── Generated .c / .h from extraction ──
	cp $(OUTPUT_DIR)/$(BUNDLE_C_STEM).c $(SNAPSHOT_DIR)/
	cp $(OUTPUT_DIR)/$(BUNDLE_C_STEM).h $(SNAPSHOT_DIR)/
	@mkdir -p $(SNAPSHOT_DIR)/internal
	cp $(OUTPUT_DIR)/internal/FStar_Pulse_PulseCore_Prims.h $(SNAPSHOT_DIR)/internal/
	cp $(OUTPUT_DIR)/internal/Prims.h                       $(SNAPSHOT_DIR)/internal/
	@# ── Handwritten test driver ──
	cp main.c $(SNAPSHOT_DIR)/main.c
	@# ── KaRaMeL runtime headers ──
	@mkdir -p $(SNAPSHOT_DIR)/krmllib/krml/internal
	cp $(KRML_HOME)/include/krmllib.h              $(SNAPSHOT_DIR)/krmllib/
	cp $(KRML_HOME)/include/krml/fstar_int.h       $(SNAPSHOT_DIR)/krmllib/krml/
	cp $(KRML_HOME)/include/krml/lowstar_endianness.h $(SNAPSHOT_DIR)/krmllib/krml/
	cp $(KRML_HOME)/include/krml/internal/builtin.h   $(SNAPSHOT_DIR)/krmllib/krml/internal/
	cp $(KRML_HOME)/include/krml/internal/callconv.h  $(SNAPSHOT_DIR)/krmllib/krml/internal/
	cp $(KRML_HOME)/include/krml/internal/compat.h    $(SNAPSHOT_DIR)/krmllib/krml/internal/
	cp $(KRML_HOME)/include/krml/internal/debug.h     $(SNAPSHOT_DIR)/krmllib/krml/internal/
	cp $(KRML_HOME)/include/krml/internal/target.h    $(SNAPSHOT_DIR)/krmllib/krml/internal/
	cp $(KRML_HOME)/include/krml/internal/types.h     $(SNAPSHOT_DIR)/krmllib/krml/internal/
	@# ── KaRaMeL runtime C sources (generic) ──
	@mkdir -p $(SNAPSHOT_DIR)/krmllib/dist/generic
	cp $(KRML_HOME)/krmllib/dist/generic/prims.c        $(SNAPSHOT_DIR)/krmllib/dist/generic/
	cp $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c  $(SNAPSHOT_DIR)/krmllib/dist/generic/
	cp $(KRML_HOME)/krmllib/dist/generic/Prims.h        $(SNAPSHOT_DIR)/krmllib/dist/generic/
	cp $(KRML_HOME)/krmllib/dist/generic/FStar_Int32.h  $(SNAPSHOT_DIR)/krmllib/dist/generic/
	@# ── KaRaMeL runtime headers (minimal) ──
	@mkdir -p $(SNAPSHOT_DIR)/krmllib/dist/minimal
	cp $(KRML_HOME)/krmllib/dist/minimal/FStar_UInt128.h        $(SNAPSHOT_DIR)/krmllib/dist/minimal/
	cp $(KRML_HOME)/krmllib/dist/minimal/FStar_UInt_8_16_32_64.h $(SNAPSHOT_DIR)/krmllib/dist/minimal/
	cp $(KRML_HOME)/krmllib/dist/minimal/LowStar_Endianness.h   $(SNAPSHOT_DIR)/krmllib/dist/minimal/
	cp $(KRML_HOME)/krmllib/dist/minimal/fstar_uint128_gcc64.h  $(SNAPSHOT_DIR)/krmllib/dist/minimal/
	@echo "Snapshot ready in $(SNAPSHOT_DIR)/"
