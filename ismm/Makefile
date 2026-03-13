# Makefile for ISMM: Verified Reference Counting for Deeply Immutable Data Structures
#
# Uses F* and Pulse from sibling submodules (../FStar, ../pulse).
# Follows the same conventions as autoclrs/ch*/Makefile.

PULSE_ROOT ?= ../pulse

ifndef FSTAR_EXE
FSTAR_EXE := $(CURDIR)/../FStar/bin/fstar.exe
endif
export FSTAR_EXE

# KaRaMeL for C extraction
KRML_HOME ?= $(HOME)/ws2/FunFM/tools/krml/karamel
KRML_EXE  ?= $(KRML_HOME)/krml

include $(PULSE_ROOT)/mk/test.mk

# Include autoclrs common utilities (predicates, list lemmas, etc.)
OTHERFLAGS += --include ../autoclrs/common

# ============================================================================
# C Extraction via KaRaMeL
# ============================================================================

EXTRACT_DIR = _extract

# All Pulse implementation modules to extract
ISMM_MODULES = \
  ISMM.Status \
  ISMM.Count \
  ISMM.Graph \
  ISMM.UnionFind.Spec \
  ISMM.UnionFind.Impl \
  ISMM.UnionFind.Compress \
  ISMM.UnionFind.Union \
  ISMM.UF.Lemmas \
  ISMM.UF.SizeRank \
  ISMM.Arith.Lemmas \
  ISMM.Freeze.Spec \
  ISMM.Freeze.Impl \
  ISMM.Dispose.Spec \
  ISMM.Dispose.Helpers \
  ISMM.Dispose.Setup \
  ISMM.Dispose.Inner \
  ISMM.Dispose.ProcessSCC \
  ISMM.Dispose.Loop \
  ISMM.Dispose.Impl \
  ISMM.RefCount.Spec \
  ISMM.RefCount.Impl \
  ISMM.Test \
  ISMM.Exports

$(EXTRACT_DIR):
	mkdir -p $@ $@/internal

# Step 1: Extract each module to .krml
extract-krml: all | $(EXTRACT_DIR)
	@echo "=== Extracting ISMM modules to .krml ==="
	@for mod in $(ISMM_MODULES); do \
		krml_file=$(OUTPUT_DIR)/$$(echo $$mod | tr '.' '_').krml; \
		fst_file=$$mod.fst; \
		if [ -f "$$fst_file" ]; then \
			echo "  Extracting $$mod"; \
			$(FSTAR) --codegen krml --extract_module $$mod $$fst_file; \
			if [ -f $(OUTPUT_DIR)/out.krml ]; then \
				mv -f $(OUTPUT_DIR)/out.krml $$krml_file; \
			fi; \
		fi; \
	done
	@echo ".krml files written to $(OUTPUT_DIR)/"

# Step 2: .krml → C via KaRaMeL
#   Bundle all ISMM modules into a single ISMM.c, rooting at the four
#   public API modules + test so nothing gets dead-code-eliminated.
extract-c: extract-krml | $(EXTRACT_DIR)
	@echo "=== Running KaRaMeL ==="
	@rm -rf $(EXTRACT_DIR)/*
	@mkdir -p $(EXTRACT_DIR)/internal
	$(KRML_EXE) \
		-tmpdir $(EXTRACT_DIR) \
		-skip-compilation \
		-warn-error -2-9-11-15-17 \
		-bundle 'ISMM.Exports+ISMM.Test=ISMM.*,Prims,FStar.*,Pulse.*,PulseCore.*[rename=ISMM]' \
		-no-prefix ISMM.UnionFind.Impl \
		-no-prefix ISMM.Freeze.Impl \
		-no-prefix ISMM.Dispose.Impl \
		-no-prefix ISMM.Dispose.Helpers \
		-no-prefix ISMM.Dispose.Setup \
		-no-prefix ISMM.Dispose.Inner \
		-no-prefix ISMM.Dispose.ProcessSCC \
		-no-prefix ISMM.Dispose.Loop \
		-no-prefix ISMM.RefCount.Impl \
		-no-prefix ISMM.Test \
		-no-prefix ISMM.Exports \
		$(wildcard $(OUTPUT_DIR)/ISMM_*.krml) \
		$(KRML_HOME)/krmllib/.extract/*.krml
	@echo "C files written to $(EXTRACT_DIR)/"
	@ls $(EXTRACT_DIR)/*.c $(EXTRACT_DIR)/*.h 2>/dev/null || true

# Shorthand
.PHONY: extract extract-krml extract-c test-c update-snapshot

extract: extract-c

# Step 3: Compile and run extracted C test
test-c: extract-c
	@echo "=== Compiling extracted C ==="
	gcc -std=c11 -Wall -Wno-unused-variable -Wno-parentheses \
		-Wno-implicit-function-declaration -g \
		-I$(EXTRACT_DIR) \
		-I$(KRML_HOME)/include \
		-I$(KRML_HOME)/krmllib/dist/minimal \
		-DKRML_HOST_MALLOC=malloc \
		-DKRML_HOST_FREE=free \
		-DKRML_HOST_EXIT=exit \
		-o $(EXTRACT_DIR)/test_ismm \
		$(EXTRACT_DIR)/ISMM.c _extract_stubs.c
	@echo "=== Running extracted test ==="
	$(EXTRACT_DIR)/test_ismm

# Step 4: Update snapshot directory with latest extracted C
SNAPSHOT_DIR = snapshot

update-snapshot: extract-c
	@echo "=== Updating snapshot ==="
	cp $(EXTRACT_DIR)/ISMM.c $(SNAPSHOT_DIR)/
	cp $(EXTRACT_DIR)/ISMM.h $(SNAPSHOT_DIR)/
	cp _extract_stubs.c $(SNAPSHOT_DIR)/stubs.c
	cp $(KRML_HOME)/include/krmllib.h $(SNAPSHOT_DIR)/
	cp $(KRML_HOME)/include/krml/fstar_int.h \
	   $(KRML_HOME)/include/krml/lowstar_endianness.h \
	   $(SNAPSHOT_DIR)/krml/
	cp $(KRML_HOME)/include/krml/internal/builtin.h \
	   $(KRML_HOME)/include/krml/internal/callconv.h \
	   $(KRML_HOME)/include/krml/internal/compat.h \
	   $(KRML_HOME)/include/krml/internal/debug.h \
	   $(KRML_HOME)/include/krml/internal/target.h \
	   $(KRML_HOME)/include/krml/internal/types.h \
	   $(SNAPSHOT_DIR)/krml/internal/
	cp $(KRML_HOME)/krmllib/dist/minimal/fstar_uint128_gcc64.h \
	   $(KRML_HOME)/krmllib/dist/minimal/FStar_UInt128.h \
	   $(KRML_HOME)/krmllib/dist/minimal/FStar_UInt_8_16_32_64.h \
	   $(KRML_HOME)/krmllib/dist/minimal/LowStar_Endianness.h \
	   $(SNAPSHOT_DIR)/
	@echo "Snapshot updated in $(SNAPSHOT_DIR)/"
