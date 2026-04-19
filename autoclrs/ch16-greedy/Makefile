include ../config.mk
KRML_EXE   ?= $(KRML_HOME)/krml
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch16
EXTRACT_DIR       = _output/c_extract

KRML_MODULES = \
  CLRS_Ch16_ActivitySelection_ImplTest \
  CLRS_Ch16_ActivitySelection_Impl \
  CLRS_Ch16_Huffman_ImplTest \
  CLRS_Ch16_Huffman_Impl \
  CLRS_Ch16_Huffman_Defs \
  CLRS_Ch16_Huffman_PQForest \
  Pulse_Lib_PriorityQueue \
  Pulse_Lib_ResizableVec \
  Pulse_Lib_TotalOrder \
  Pulse_Lib_Vec \
  Pulse_Lib_Box

KRML_INPUT_FILES  = $(addprefix $(OUTPUT_DIR)/,$(addsuffix .krml,$(KRML_MODULES)))
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch16.ActivitySelection.ImplTest=CLRS.Ch16.ActivitySelection.*' \
  -bundle 'CLRS.Ch16.Huffman.ImplTest=CLRS.Ch16.Huffman.*,Pulse.Lib.PriorityQueue,Pulse.Lib.ResizableVec,Pulse.Lib.TotalOrder,Pulse.Lib.Vec,Pulse.Lib.Box' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_WARN_FLAGS   = -warn-error -2-9-11-15-17-18
KRML_EXTRA_FLAGS  = -add-include '"fstar_support.h"'

# krmllib .krml files for FStar standard library types (option, order, seq).
# These are not shipped pre-built in fstar2; extract them on demand.
KRMLLIB_EXTRACT   = $(KRML_HOME)/krmllib/.extract
KRMLLIB_KRML      = $(KRMLLIB_EXTRACT)/FStar_Pervasives_Native.krml \
                    $(KRMLLIB_EXTRACT)/FStar_Order.krml \
                    $(KRMLLIB_EXTRACT)/FStar_Seq_Base.krml
FSTAR_ULIB        = $(shell dirname $$(readlink -f $(FSTAR_EXE)))/../lib/fstar/ulib

$(KRMLLIB_EXTRACT)/FStar_Pervasives_Native.krml: | $(KRMLLIB_EXTRACT)
	$(FSTAR_EXE) --no_cmi --odir $(KRMLLIB_EXTRACT) --codegen krml \
	  --extract_module FStar.Pervasives.Native \
	  $(FSTAR_ULIB)/FStar.Pervasives.Native.fst

$(KRMLLIB_EXTRACT)/FStar_Order.krml: | $(KRMLLIB_EXTRACT)
	$(FSTAR_EXE) --no_cmi --odir $(KRMLLIB_EXTRACT) --codegen krml \
	  --extract_module FStar.Order \
	  $(FSTAR_ULIB)/FStar.Order.fst

$(KRMLLIB_EXTRACT)/FStar_Seq_Base.krml: | $(KRMLLIB_EXTRACT)
	$(FSTAR_EXE) --no_cmi --odir $(KRMLLIB_EXTRACT) --codegen krml \
	  --extract_module FStar.Seq.Base \
	  $(FSTAR_ULIB)/FStar.Seq.Base.fst

$(KRMLLIB_EXTRACT):
	mkdir -p $@

KRML_EXTRA_INPUTS = $(KRMLLIB_KRML)

# KaRaMeL produces multiple .c files
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch16_ActivitySelection_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch16_Huffman_ImplTest.c \
                    $(EXTRACT_DIR)/FStar_Pulse_PulseCore_Prims.c
# Note: CLRS.Ch16.Huffman.Codec.ImplTest is NOT extracted because
# Codec.Impl functions (decode_impl, encode_impl, free_htree) take
# HSpec.htree as a non-erased parameter for runtime tree traversal,
# making them non-extractable to C via KaRaMeL. The Codec ImplTest
# IS fully verified with machine-checked proofs (see Codec.ImplTest.fst).
EXTRA_C_SOURCES   = fstar_support.c \
                    $(KRML_HOME)/krmllib/dist/generic/prims.c
CC_EXTRA_FLAGS    = -Wno-unused-but-set-variable
CC_EXTRA_INCLUDES = -I $(EXTRACT_DIR)/internal

include ../autoclrs.test.mk

# Ensure krmllib .krml files are built before KaRaMeL extraction
$(firstword $(EXTRACT_C_FILES)): $(KRMLLIB_KRML)

# ── Snapshot target: self-contained C directory ──────────────────────
#
# Produces snapshot/ with all extracted + handwritten C sources and a
# standalone Makefile that can build and run the tests without F*/KaRaMeL.

SNAPSHOT_DIR = snapshot

.PHONY: snapshot
snapshot: extract
	@echo "[SNAPSHOT] Populating $(SNAPSHOT_DIR)/"
	@rm -rf $(SNAPSHOT_DIR)
	@mkdir -p $(SNAPSHOT_DIR)/internal $(SNAPSHOT_DIR)/krml/internal
	@# ── Generated files (F* + KaRaMeL) ──
	@cp $(EXTRACT_DIR)/CLRS_Ch16_ActivitySelection_ImplTest.c $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch16_ActivitySelection_ImplTest.h $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch16_Huffman_ImplTest.c           $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch16_Huffman_ImplTest.h           $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/FStar_Pulse_PulseCore_Prims.c          $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/internal/CLRS_Ch16_Huffman_ImplTest.h  $(SNAPSHOT_DIR)/internal/
	@cp $(EXTRACT_DIR)/internal/FStar_Pulse_PulseCore_Prims.h $(SNAPSHOT_DIR)/internal/
	@# ── krmllib support headers (karamel/include tree) ──
	@cp $(KRML_HOME)/include/krmllib.h                  $(SNAPSHOT_DIR)/
	@cp $(KRML_HOME)/include/krml/lowstar_endianness.h  $(SNAPSHOT_DIR)/krml/
	@cp $(KRML_HOME)/include/krml/fstar_int.h           $(SNAPSHOT_DIR)/krml/
	@cp $(KRML_HOME)/include/krml/internal/target.h     $(SNAPSHOT_DIR)/krml/internal/
	@cp $(KRML_HOME)/include/krml/internal/callconv.h   $(SNAPSHOT_DIR)/krml/internal/
	@cp $(KRML_HOME)/include/krml/internal/builtin.h    $(SNAPSHOT_DIR)/krml/internal/
	@cp $(KRML_HOME)/include/krml/internal/debug.h      $(SNAPSHOT_DIR)/krml/internal/
	@cp $(KRML_HOME)/include/krml/internal/types.h      $(SNAPSHOT_DIR)/krml/internal/
	@cp $(KRML_HOME)/include/krml/internal/compat.h     $(SNAPSHOT_DIR)/krml/internal/
	@# ── krmllib/dist/minimal headers (uint128, endianness — at root for -I .) ──
	@cp $(KRML_HOME)/krmllib/dist/minimal/fstar_uint128_gcc64.h              $(SNAPSHOT_DIR)/
	@cp $(KRML_HOME)/krmllib/dist/minimal/fstar_uint128_msvc.h               $(SNAPSHOT_DIR)/
	@cp $(KRML_HOME)/krmllib/dist/minimal/fstar_uint128_struct_endianness.h  $(SNAPSHOT_DIR)/
	@cp $(KRML_HOME)/krmllib/dist/minimal/FStar_UInt128_Verified.h           $(SNAPSHOT_DIR)/
	@cp $(KRML_HOME)/krmllib/dist/minimal/FStar_UInt_8_16_32_64.h           $(SNAPSHOT_DIR)/
	@cp $(KRML_HOME)/krmllib/dist/minimal/FStar_UInt128.h                   $(SNAPSHOT_DIR)/
	@cp $(KRML_HOME)/krmllib/dist/minimal/LowStar_Endianness.h             $(SNAPSHOT_DIR)/
	@# ── krmllib runtime C sources / headers ──
	@cp $(KRML_HOME)/krmllib/dist/generic/prims.c       $(SNAPSHOT_DIR)/
	@cp $(KRML_HOME)/krmllib/dist/generic/Prims.h       $(SNAPSHOT_DIR)/
	@cp $(KRML_HOME)/krmllib/dist/generic/FStar_Int32.h $(SNAPSHOT_DIR)/
	@# ── Handwritten files (copy with HANDWRITTEN banner) ──
	@for f in main.c fstar_support.c fstar_support.h; do \
	  ( echo "/* !!  HANDWRITTEN  !!"; \
	    echo " * This file is NOT generated by F* + KaRaMeL."; \
	    echo " * It was written by hand as part of the Ch16 test harness."; \
	    echo " */"; \
	    echo ""; \
	    cat $$f; \
	  ) > $(SNAPSHOT_DIR)/$$f; \
	done
	@# ── Standalone Makefile ──
	@cp snapshot.Makefile $(SNAPSHOT_DIR)/Makefile
	@echo "[SNAPSHOT] Done — build with:  make -C $(SNAPSHOT_DIR)"
