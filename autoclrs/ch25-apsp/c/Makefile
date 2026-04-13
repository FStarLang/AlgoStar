# autoclrs/ch25-apsp/c/Makefile
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

# Parent ch25 directory (for CLRS.Ch25.* modules)
CH25_DIR   := $(CURDIR)/..
COMMON_DIR := $(CURDIR)/../../common

# Detect binary install vs source build for fstar.exe
ifneq ($(wildcard $(ROOT)/FStar/bin/fstar.exe),)
  FSTAR_EXE ?= $(ROOT)/FStar/bin/fstar.exe
else ifneq ($(wildcard $(ROOT)/fstar/bin/fstar.exe),)
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
	--include $(CH25_DIR) \
	--include $(CH25_DIR)/_cache \
	--include $(COMMON_DIR) \
	--z3rlimit 80 \
	--already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,PulseCore,CLRS.Ch25.FloydWarshall

# ── Source files ───────────────────────────────────────────────────
C_FILES := $(wildcard *.c)

# Convert foo.c → Foo.fst (capitalize first letter)
c_to_fst = $(shell echo '$(1)' | sed 's/^\(.\)/\U\1/;s/\.c$$/.fst/')

FST_FILES := $(foreach f,$(C_FILES),$(call c_to_fst,$(f)))
CHECKED   := $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(FST_FILES)))

# Also verify any hand-written .fst/.fsti helper modules
HELPER_FST  := $(wildcard *.fst) $(wildcard *.fsti)
HELPER_CHECKED := $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(HELPER_FST)))

# ── Rules ──────────────────────────────────────────────────────────

# Generate per-file rules: FloydWarshall.fst: floydWarshall.c $(C2PULSE) c2pulse.h
define make_fst_rule
$(call c_to_fst,$(1)): $(1) $$(C2PULSE) c2pulse.h
endef
$(foreach f,$(C_FILES),$(eval $(call make_fst_rule,$(f))))

# c2pulse: .c → .fst
%.fst:
	$(C2PULSE) $<

# fstar: .fst → .checked
$(CACHE_DIR)/%.fst.checked: %.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) --force $<
	@touch $@

$(CACHE_DIR)/%.fsti.checked: %.fsti
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) --force $<
	@touch $@

verify: $(CHECKED) $(HELPER_CHECKED)

clean:
	rm -rf $(CACHE_DIR) $(FST_FILES) *_diagnostics.json *_source_range_info.json
