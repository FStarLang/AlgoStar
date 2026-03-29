PULSE_ROOT ?= ../../FStar/pulse
include $(PULSE_ROOT)/mk/test.mk
OTHERFLAGS += --include ../common

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID  = ch32
EXTRACT_DIR = _extract

EXTRACT_MODULES = \
  CLRS.Ch32.NaiveStringMatch.ImplTest \
  CLRS.Ch32.NaiveStringMatch \
  CLRS.Ch32.NaiveStringMatch.Spec \
  CLRS.Ch32.NaiveStringMatch.Lemmas \
  CLRS.Ch32.NaiveStringMatch.Complexity \
  CLRS.Ch32.KMP.ImplTest \
  CLRS.Ch32.KMP \
  CLRS.Ch32.KMP.Bridge \
  CLRS.Ch32.KMP.PureDefs \
  CLRS.Ch32.KMP.Spec \
  CLRS.Ch32.RabinKarp.ImplTest \
  CLRS.Ch32.RabinKarp \
  CLRS.Ch32.RabinKarp.Spec \
  CLRS.Ch32.RabinKarp.Lemmas \
  CLRS.Ch32.RabinKarp.Complexity \
  CLRS.Common.Complexity

# Step 1: extract all modules to .krml (shell loop)
extract-krml: __verify
	@mkdir -p $(EXTRACT_DIR)
	@for mod in $(EXTRACT_MODULES); do \
	  krml_file=$(OUTPUT_DIR)/$$(echo $$mod | tr '.' '_').krml; \
	  printf "   %-14s  %s\n" "EXTRACT" "$$mod"; \
	  $(FSTAR) _cache/$$mod.fst.checked --codegen krml --extract_module $$mod; \
	done

KRML_INPUT_FILES  = $(foreach m,$(EXTRACT_MODULES),$(OUTPUT_DIR)/$(subst .,_,$(m)).krml)
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch32.NaiveStringMatch.ImplTest+CLRS.Ch32.KMP.ImplTest+CLRS.Ch32.RabinKarp.ImplTest+CLRS.Ch32.NaiveStringMatch+CLRS.Ch32.KMP+CLRS.Ch32.RabinKarp+CLRS.Ch32.RabinKarp.Spec+CLRS.Ch32.NaiveStringMatch.Spec+CLRS.Ch32.NaiveStringMatch.Lemmas+CLRS.Ch32.NaiveStringMatch.Complexity+CLRS.Ch32.KMP.Bridge+CLRS.Ch32.KMP.PureDefs+CLRS.Ch32.KMP.Spec+CLRS.Ch32.RabinKarp.Lemmas+CLRS.Ch32.RabinKarp.Complexity+CLRS.Common.Complexity=[rename=Ch32_StringMatch]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_EXTRA_FLAGS  = \
  -no-prefix 'CLRS.Ch32.NaiveStringMatch.ImplTest' \
  -no-prefix 'CLRS.Ch32.KMP.ImplTest' \
  -no-prefix 'CLRS.Ch32.RabinKarp.ImplTest' \
  -no-prefix 'CLRS.Ch32.NaiveStringMatch' \
  -no-prefix 'CLRS.Ch32.KMP' \
  -no-prefix 'CLRS.Ch32.RabinKarp'
KRML_EXTRA_INPUTS = $(KRML_HOME)/krmllib/.extract/*.krml
EXTRACT_C_FILES   = $(EXTRACT_DIR)/Ch32_StringMatch.c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c
CC_EXTRA_FLAGS    = -Wno-unused-function -include ch32_shims.h
CC_EXTRA_INCLUDES = -I $(EXTRACT_DIR)/internal

include ../autoclrs.test.mk

# Override: extraction depends on the shell-loop step
$(firstword $(EXTRACT_C_FILES)): extract-krml

clean: __clean_extract
.PHONY: __clean_extract
__clean_extract:
	rm -rf $(EXTRACT_DIR)
