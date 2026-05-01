include ../config.mk
include $(PULSE_ROOT)/mk/test.mk
OTHERFLAGS += --include ../common

# ââ C extraction and test targets ââââââââââââââââââââââââââââââââââââââââââââ
CHAPTER_ID  = ch32
EXTRACT_DIR = _extract

# Only Impl + ImplTest modules are extracted to C.
# Spec/Lemma/Complexity/Bridge modules are proof-only (not extracted).
EXTRACT_MODULES = \
  CLRS.Ch32.NaiveStringMatch.ImplTest \
  CLRS.Ch32.NaiveStringMatch \
  CLRS.Ch32.KMP.ImplTest \
  CLRS.Ch32.KMP \
  CLRS.Ch32.RabinKarp.ImplTest \
  CLRS.Ch32.RabinKarp

KRML_INPUT_FILES = $(foreach m,$(EXTRACT_MODULES),$(OUTPUT_DIR)/$(subst .,_,$(m)).krml)

KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch32.NaiveStringMatch.ImplTest+CLRS.Ch32.KMP.ImplTest+CLRS.Ch32.RabinKarp.ImplTest+CLRS.Ch32.NaiveStringMatch+CLRS.Ch32.KMP+CLRS.Ch32.RabinKarp=[rename=Ch32_StringMatch]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_EXTRA_FLAGS  = \
  -no-prefix 'CLRS.Ch32.NaiveStringMatch.ImplTest' \
  -no-prefix 'CLRS.Ch32.KMP.ImplTest' \
  -no-prefix 'CLRS.Ch32.RabinKarp.ImplTest' \
  -no-prefix 'CLRS.Ch32.NaiveStringMatch' \
  -no-prefix 'CLRS.Ch32.KMP' \
  -no-prefix 'CLRS.Ch32.RabinKarp'
KRML_EXTRA_INPUTS =
EXTRACT_C_FILES   = $(EXTRACT_DIR)/Ch32_StringMatch.c
# prims.c provides Prims_op_* (checked int arithmetic used by RabinKarp's int/nat computations)
# fstar_int32.c provides FStar_Int32_to_string (dependency of prims.c)
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c
CC_EXTRA_FLAGS    = -Wno-unused-function -include ch32_shims.h
CC_EXTRA_INCLUDES = -I $(EXTRACT_DIR)/internal

# Cancel Pulse's generic pattern rules for the extract dir
$(EXTRACT_DIR)/%.krml:
	@true
$(EXTRACT_DIR)/%.c: $(EXTRACT_DIR)/%.krml
	@true

include ../autoclrs.test.mk

# ── Snapshot target ──────────────────────────────────────────────────
# Produces a self-contained snapshot/ directory with all generated C code,
# handwritten test driver, and the minimal krmllib headers needed to build
# and run standalone (no F*/KaRaMeL installation required).

SNAPSHOT_DIR = snapshot
KRML_INCLUDE = $(KRML_HOME)/include
KRML_DIST_MIN = $(KRML_HOME)/krmllib/dist/minimal
KRML_DIST_GEN = $(KRML_HOME)/krmllib/dist/generic

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES)
	$(call msg, "SNAPSHOT", "$(CHAPTER_ID)")
	@rm -rf $(SNAPSHOT_DIR)
	@mkdir -p $(SNAPSHOT_DIR)/internal
	@mkdir -p $(SNAPSHOT_DIR)/krmllib/krml/internal
	@mkdir -p $(SNAPSHOT_DIR)/krmllib/dist/generic
	@mkdir -p $(SNAPSHOT_DIR)/krmllib/dist/minimal
	@# ── Generated files (F* + KaRaMeL) ──
	@cp $(EXTRACT_DIR)/Ch32_StringMatch.c $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/Ch32_StringMatch.h $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/internal/FStar_Pulse_PulseCore_Prims.h $(SNAPSHOT_DIR)/internal/
	@# ── Handwritten files ──
	@{ echo '/* HANDWRITTEN: This is a manually written test driver, not generated code. */'; \
	   cat main.c; } > $(SNAPSHOT_DIR)/main.c
	@{ echo '/* HANDWRITTEN: This is a manually written shim header, not generated code. */'; \
	   cat ch32_shims.h; } > $(SNAPSHOT_DIR)/ch32_shims.h
	@# ── KaRaMeL runtime support ──
	@cp $(KRML_INCLUDE)/krmllib.h $(SNAPSHOT_DIR)/krmllib/
	@cp $(KRML_INCLUDE)/krml/fstar_int.h $(SNAPSHOT_DIR)/krmllib/krml/
	@cp $(KRML_INCLUDE)/krml/lowstar_endianness.h $(SNAPSHOT_DIR)/krmllib/krml/
	@for f in builtin.h callconv.h compat.h debug.h target.h types.h; do \
	   cp $(KRML_INCLUDE)/krml/internal/$$f $(SNAPSHOT_DIR)/krmllib/krml/internal/; \
	 done
	@cp $(KRML_DIST_GEN)/prims.c $(KRML_DIST_GEN)/Prims.h \
	    $(KRML_DIST_GEN)/fstar_int32.c $(KRML_DIST_GEN)/FStar_Int32.h \
	    $(SNAPSHOT_DIR)/krmllib/dist/generic/
	@for f in $(KRML_DIST_MIN)/*.h; do \
	   cp $$f $(SNAPSHOT_DIR)/krmllib/dist/minimal/; \
	 done
	@# ── Snapshot Makefile ──
	@cp snapshot.Makefile $(SNAPSHOT_DIR)/Makefile
	@echo "Snapshot created in $(SNAPSHOT_DIR)/"

clean: __clean_extract
.PHONY: __clean_extract
__clean_extract:
	rm -rf $(EXTRACT_DIR) $(SNAPSHOT_DIR)
