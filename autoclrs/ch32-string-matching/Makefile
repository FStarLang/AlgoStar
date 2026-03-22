PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk
# Undo optimize_let_vc and fly_deps — they break proofs in KMP.Complexity.fst
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --ext optimize_let_vc=false --ext fly_deps=false --include ../common

# ============================================================================
# C extraction and testing (ImplTest modules)
# ============================================================================

KRML_HOME ?= ../../krml/karamel
EXTRACT_DIR = _extract

# Modules to extract to .krml
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

KRML_FILES = $(foreach m,$(EXTRACT_MODULES),$(OUTPUT_DIR)/$(subst .,_,$(m)).krml)

# Step 1: Extract all modules to .krml
extract-krml: __verify
	@for mod in $(EXTRACT_MODULES); do \
	  krml_file=$(OUTPUT_DIR)/$$(echo $$mod | tr '.' '_').krml; \
	  printf "   %-14s  %s\n" "EXTRACT" "$$mod"; \
	  $(FSTAR) _cache/$$mod.fst.checked --codegen krml --extract_module $$mod; \
	done

# Step 2: KaRaMeL .krml -> .c
$(EXTRACT_DIR)/Ch32_StringMatch.c: extract-krml | $(EXTRACT_DIR)
	$(call msg, "KRML", "Ch32_StringMatch")
	$(KRML_HOME)/krml \
	  -tmpdir $(EXTRACT_DIR) \
	  -skip-compilation \
	  -skip-makefiles \
	  -warn-error -2-9-11-15-17 \
	  -bundle 'CLRS.Ch32.NaiveStringMatch.ImplTest+CLRS.Ch32.KMP.ImplTest+CLRS.Ch32.RabinKarp.ImplTest+CLRS.Ch32.NaiveStringMatch+CLRS.Ch32.KMP+CLRS.Ch32.RabinKarp+CLRS.Ch32.RabinKarp.Spec+CLRS.Ch32.NaiveStringMatch.Spec+CLRS.Ch32.NaiveStringMatch.Lemmas+CLRS.Ch32.NaiveStringMatch.Complexity+CLRS.Ch32.KMP.Bridge+CLRS.Ch32.KMP.PureDefs+CLRS.Ch32.KMP.Spec+CLRS.Ch32.RabinKarp.Lemmas+CLRS.Ch32.RabinKarp.Complexity+CLRS.Common.Complexity=[rename=Ch32_StringMatch]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -no-prefix 'CLRS.Ch32.NaiveStringMatch.ImplTest' \
	  -no-prefix 'CLRS.Ch32.KMP.ImplTest' \
	  -no-prefix 'CLRS.Ch32.RabinKarp.ImplTest' \
	  -no-prefix 'CLRS.Ch32.NaiveStringMatch' \
	  -no-prefix 'CLRS.Ch32.KMP' \
	  -no-prefix 'CLRS.Ch32.RabinKarp' \
	  $(KRML_FILES) \
	  $(KRML_HOME)/krmllib/.extract/*.krml

$(EXTRACT_DIR):
	mkdir -p $@

# Step 3: Compile and link
KRML_CFLAGS = -I $(KRML_HOME)/include \
              -I $(KRML_HOME)/krmllib/dist/generic \
              -I $(EXTRACT_DIR) \
              -I $(EXTRACT_DIR)/internal

$(EXTRACT_DIR)/Ch32_StringMatch.o: $(EXTRACT_DIR)/Ch32_StringMatch.c ch32_shims.h
	$(call msg, "CC", "Ch32_StringMatch.c")
	$(CC) -c -Wall -Wno-unused-function $(KRML_CFLAGS) \
	  -include ch32_shims.h \
	  $< -o $@

$(EXTRACT_DIR)/main.o: main.c $(EXTRACT_DIR)/Ch32_StringMatch.c
	$(call msg, "CC", "main.c")
	$(CC) -c -Wall $(KRML_CFLAGS) $< -o $@

$(EXTRACT_DIR)/ch32_test: $(EXTRACT_DIR)/Ch32_StringMatch.o $(EXTRACT_DIR)/main.o
	$(call msg, "LINK", "ch32_test")
	$(CC) $^ \
	  $(KRML_HOME)/krmllib/dist/generic/prims.c \
	  $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c \
	  -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/generic \
	  -o $@

# Public targets
.PHONY: extract test
extract: $(EXTRACT_DIR)/Ch32_StringMatch.c
test: $(EXTRACT_DIR)/ch32_test
	$(call msg, "RUN", "ch32_test")
	$(EXTRACT_DIR)/ch32_test

clean: __clean_extract
.PHONY: __clean_extract
__clean_extract:
	rm -rf $(EXTRACT_DIR)
