# autoclrs/ch04-divide-conquer/c/Makefile
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

# Parent ch04 directory (for CLRS.Ch04.* modules)
CH04_DIR   := $(CURDIR)/..
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
	--include $(CH04_DIR) \
	--include $(COMMON_DIR) \
	--z3rlimit 40 \
	--already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore

# ── Source files ───────────────────────────────────────────────────
C_FILES := $(wildcard *.c)

# MatrixMultiply.fst is hand-edited (not c2pulse-generated) because
# functional correctness proofs require pinned_array, id #int, and
# opaque interface patterns that c2pulse cannot generate.
HAND_EDITED_FST := MatrixMultiply.fst

# Convert foo.c → Foo.fst (capitalize first letter)
c_to_fst = $(shell echo '$(1)' | sed 's/^\(.\)/\U\1/;s/\.c$$/.fst/')

# Exclude hand-edited files from c2pulse generation
C2PULSE_C_FILES := $(filter-out $(foreach f,$(HAND_EDITED_FST),$(shell echo '$(f)' | sed 's/^\(.\)/\L\1/;s/\.fst$$/.c/')),$(C_FILES))
FST_FILES := $(foreach f,$(C2PULSE_C_FILES),$(call c_to_fst,$(f))) $(HAND_EDITED_FST)
CHECKED   := $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(FST_FILES)))

# Also verify any hand-written .fst helper modules
HELPER_FST := $(wildcard *.fst)
HELPER_CHECKED := $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(HELPER_FST)))

# ── Rules ──────────────────────────────────────────────────────────

# Generate per-file rules: BinarySearch.fst: BinarySearch.c $(C2PULSE) c2pulse.h
define make_fst_rule
$(call c_to_fst,$(1)): $(1) $$(C2PULSE) c2pulse.h
endef
$(foreach f,$(C2PULSE_C_FILES),$(eval $(call make_fst_rule,$(f))))

# c2pulse: .c → .fst
%.fst:
	$(C2PULSE) $<

# fstar: .fst → .checked
$(CACHE_DIR)/%.fst.checked: %.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) --force $<
	@touch $@

verify: $(CHECKED) $(HELPER_CHECKED)

clean:
	rm -rf $(CACHE_DIR) $(foreach f,$(C2PULSE_C_FILES),$(call c_to_fst,$(f)))
