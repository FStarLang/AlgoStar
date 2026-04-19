include ../config.mk
OTHERFLAGS += --include ../common
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID         = ch31

EXTRACT_MODULES = \
  CLRS.Ch31.GCD.ImplTest \
  CLRS.Ch31.GCD.Impl \
  CLRS.Ch31.GCD.Spec \
  CLRS.Ch31.GCD.Complexity \
  CLRS.Ch31.GCD.Lemmas \
  CLRS.Ch31.ExtendedGCD.ImplTest \
  CLRS.Ch31.ExtendedGCD.Impl \
  CLRS.Ch31.ExtendedGCD.Spec \
  CLRS.Ch31.ExtendedGCD.Complexity \
  CLRS.Ch31.ExtendedGCD.Lemmas \
  CLRS.Ch31.ModExp.ImplTest \
  CLRS.Ch31.ModExp.Impl \
  CLRS.Ch31.ModExp.Spec \
  CLRS.Ch31.ModExp.Complexity \
  CLRS.Ch31.ModExp.Lemmas \
  CLRS.Ch31.ModExpLR.ImplTest \
  CLRS.Ch31.ModExpLR.Impl \
  CLRS.Ch31.ModExpLR.Complexity \
  CLRS.Ch31.ModExpLR.Lemmas \
  CLRS.Common.Complexity

BUNDLE_C_STEM = Ch31_NumberTheory

KRML_INPUT_FILES  = $(foreach m,$(EXTRACT_MODULES),$(OUTPUT_DIR)/$(subst .,_,$m).krml)
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch31.GCD.ImplTest+CLRS.Ch31.ExtendedGCD.ImplTest+CLRS.Ch31.ModExp.ImplTest+CLRS.Ch31.ModExpLR.ImplTest=CLRS.*[rename=Ch31_NumberTheory]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_WARN_FLAGS   = -warn-error -2-9-15-17
KRML_EXTRA_INPUTS =
EXTRACT_C_FILES   = $(OUTPUT_DIR)/$(BUNDLE_C_STEM).c
EXTRA_C_SOURCES   =
CC_EXTRA_FLAGS    =

include ../autoclrs.test.mk

# ── Snapshot target ─────────────────────────────────────────────────
# Produces a self-contained C distribution in snapshot/ that can be
# built with just a C compiler (no F*, Pulse, or KaRaMeL required).

SNAPSHOT_DIR = snapshot
KRML_INCLUDE_DIR = $(KRML_HOME)/include

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES)
	@echo "  [SNAPSHOT] Creating $(SNAPSHOT_DIR)/"
	@rm -rf $(SNAPSHOT_DIR)
	@mkdir -p $(SNAPSHOT_DIR)
	cp $(OUTPUT_DIR)/$(BUNDLE_C_STEM).c $(SNAPSHOT_DIR)/
	cp $(OUTPUT_DIR)/$(BUNDLE_C_STEM).h $(SNAPSHOT_DIR)/
	cp $(TEST_MAIN) $(SNAPSHOT_DIR)/
	cp -r $(KRML_INCLUDE_DIR)/krmllib.h $(SNAPSHOT_DIR)/
	cp -r $(KRML_INCLUDE_DIR)/krml $(SNAPSHOT_DIR)/
	@# Copy krmllib uint128 / endianness support headers (transitively included)
	cp $(KRML_HOME)/krmllib/dist/minimal/*.h $(SNAPSHOT_DIR)/
	cp snapshot.Makefile $(SNAPSHOT_DIR)/Makefile
	@echo "  [SNAPSHOT] Done — build with: cd $(SNAPSHOT_DIR) && make test"
