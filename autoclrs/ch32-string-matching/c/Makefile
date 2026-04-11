# autoclrs/ch32-string-matching/c/Makefile
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

# Parent ch32 directory (for CLRS.Ch32.* and CLRS.Common.* modules)
CH32_DIR   := $(CURDIR)/..
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
	--include $(CH32_DIR) \
	--include $(COMMON_DIR) \
	--z3rlimit 40 \
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

# Generate per-file rules: NaiveStringMatch.fst: naiveStringMatch.c $(C2PULSE) c2pulse.h
define make_fst_rule
$(call c_to_fst,$(1)): $(1) $$(C2PULSE) c2pulse.h
endef
$(foreach f,$(C_FILES),$(eval $(call make_fst_rule,$(f))))

# c2pulse: .c → .fst
%.fst:
	$(C2PULSE) $<

# Per-file z3rlimit overrides (default 40 is too low for complex files)
EXTRA_FSTAR_NaiveStringMatch.fst = --z3rlimit 400 --fuel 4 --ifuel 2
EXTRA_FSTAR_RabinKarp.fst = --z3rlimit 400
EXTRA_FSTAR_KMP.fst = --z3rlimit 2000 --fuel 2 --ifuel 1

# fstar: .fst → .checked
$(CACHE_DIR)/%.fst.checked: %.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) $(EXTRA_FSTAR_$<) --force $<
	@touch $@

verify: $(CHECKED) $(HELPER_CHECKED)

clean:
	rm -rf $(CACHE_DIR) $(FST_FILES)
