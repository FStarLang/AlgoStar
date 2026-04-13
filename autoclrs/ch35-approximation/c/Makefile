# autoclrs/ch35-approximation/c/Makefile
#
# Translate annotated C to Pulse (via c2pulse) and verify with F*.
#
# Usage:
#   make          # translate + verify all .c files
#   make clean

.PHONY: all verify clean

all: verify

# ── Paths ──────────────────────────────────────────────────────────
ROOT       := $(CURDIR)/../../..
C2PULSE    := $(ROOT)/c2pulse/target/debug/c2pulse
PULSE_LIB  := $(ROOT)/c2pulse/pulse

# Parent ch35 directory (for CLRS.Ch35.* modules)
CH35_DIR   := $(CURDIR)/..
COMMON_DIR := $(CURDIR)/../../common

# Detect binary install vs source build for fstar.exe
ifneq ($(wildcard $(ROOT)/fstar/bin/fstar.exe),)
  FSTAR_EXE ?= $(ROOT)/fstar/bin/fstar.exe
else
  FSTAR_EXE ?= $(ROOT)/FStar/out/bin/fstar.exe
endif

CACHE_DIR  := _cache

FSTAR = $(FSTAR_EXE) \
	$(OTHERFLAGS) \
	--cache_checked_modules \
	--cache_dir $(CACHE_DIR) \
	--include $(PULSE_LIB) \
	--include $(CH35_DIR) \
	--include $(COMMON_DIR) \
	--z3rlimit 200 \
	--already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore

# ── Source files ───────────────────────────────────────────────────
C_FILES := $(wildcard *.c)

# Convert foo.c → Foo.fst (capitalize first letter)
c_to_fst = $(shell echo '$(1)' | sed 's/^\(.\)/\U\1/;s/\.c$$/.fst/')

FST_FILES := $(foreach f,$(C_FILES),$(call c_to_fst,$(f)))
CHECKED   := $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(FST_FILES)))

# Also verify any hand-written .fst helper modules
HELPER_FST := $(wildcard *.fst)
HELPER_CHECKED := $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(HELPER_FST)))

# ── Rules ──────────────────────────────────────────────────────────

# Generate per-file rules: ApproxVertexCover.fst: approxVertexCover.c $(C2PULSE) c2pulse.h
define make_fst_rule
$(call c_to_fst,$(1)): $(1) $$(C2PULSE) c2pulse.h
endef
$(foreach f,$(C_FILES),$(eval $(call make_fst_rule,$(f))))

# c2pulse: .c → .fst
%.fst:
	$(C2PULSE) $<

# Parent modules needed for caching (local helpers depend on these)
$(CACHE_DIR)/CLRS.Ch35.VertexCover.Spec.fst.checked: $(CH35_DIR)/CLRS.Ch35.VertexCover.Spec.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) --force $<

$(CACHE_DIR)/CLRS.Ch35.VertexCover.Lemmas.fsti.checked: $(CH35_DIR)/CLRS.Ch35.VertexCover.Lemmas.fsti $(CACHE_DIR)/CLRS.Ch35.VertexCover.Spec.fst.checked
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) --force $<

$(CACHE_DIR)/CLRS.Ch35.VertexCover.Lemmas.fst.checked: $(CH35_DIR)/CLRS.Ch35.VertexCover.Lemmas.fst $(CACHE_DIR)/CLRS.Ch35.VertexCover.Lemmas.fsti.checked
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) --force $<

# fstar: .fst → .checked
$(CACHE_DIR)/%.fst.checked: %.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) --force $<

# fstar: .fsti → .checked
$(CACHE_DIR)/%.fsti.checked: %.fsti
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) --force $<

# Also verify .fsti helper interfaces
HELPER_FSTI := $(wildcard *.fsti)
HELPER_FSTI_CHECKED := $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(HELPER_FSTI)))

verify: $(CHECKED) $(HELPER_CHECKED) $(HELPER_FSTI_CHECKED)

# ── Inter-module dependencies ──────────────────────────────────────
$(CACHE_DIR)/AVCHelper.fst.checked: $(CACHE_DIR)/CLRS.Ch35.VertexCover.Spec.fst.checked
$(CACHE_DIR)/AVCGhostStep.fst.checked: $(CACHE_DIR)/AVCHelper.fst.checked
$(CACHE_DIR)/AVCBridgeLemmas.fsti.checked: $(CACHE_DIR)/AVCHelper.fst.checked $(CACHE_DIR)/CLRS.Ch35.VertexCover.Lemmas.fsti.checked
$(CACHE_DIR)/AVCBridgeLemmas.fst.checked: $(CACHE_DIR)/AVCBridgeLemmas.fsti.checked $(CACHE_DIR)/CLRS.Ch35.VertexCover.Lemmas.fst.checked
$(CACHE_DIR)/ApproxVertexCover.fst.checked: $(CACHE_DIR)/AVCHelper.fst.checked $(CACHE_DIR)/AVCGhostStep.fst.checked $(CACHE_DIR)/AVCBridgeLemmas.fst.checked

clean:
	rm -rf $(CACHE_DIR) $(FST_FILES)
