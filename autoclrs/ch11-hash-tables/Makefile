PULSE_ROOT ?= ../../pulse
KRML_HOME ?= ../../krml/karamel
include $(PULSE_ROOT)/mk/test.mk

# ---- C extraction, compilation, and test targets ----

KRML_EXE ?= $(KRML_HOME)/krml
KRML_INCLUDE := $(KRML_HOME)/include
KRML_DIST    := $(KRML_HOME)/krmllib/dist/minimal

# Step 1: Extract ImplTest + Impl into a single .krml via F*
#   Note: --cmi is omitted because cross-module inlining interferes with
#   multi-module extraction. The FSTAR_EXTRACT variable uses FSTAR_EXE directly.
FSTAR_EXTRACT = $(FSTAR_EXE) --cache_checked_modules --odir $(OUTPUT_DIR) \
	--cache_dir $(CACHE_DIR) \
	--already_cached 'Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore' \
	--warn_error '-321' --warn_error '@247' --ext optimize_let_vc --ext fly_deps \
	--include $(PULSE_ROOT)/out/lib/pulse

$(OUTPUT_DIR)/CLRS_Ch11_HashTable_combined.krml: \
    _cache/CLRS.Ch11.HashTable.ImplTest.fst.checked \
    _cache/CLRS.Ch11.HashTable.Impl.fst.checked
	@mkdir -p $(OUTPUT_DIR)
	$(call msg, "EXTRACT", "combined.krml")
	$(FSTAR_EXTRACT) \
	  CLRS.Ch11.HashTable.ImplTest.fst \
	  --codegen krml \
	  --extract_module CLRS.Ch11.HashTable.Impl \
	  --extract_module CLRS.Ch11.HashTable.ImplTest \
	  -o $@

# Step 2: Run KaRaMeL to produce .c/.h from the combined .krml
#   - Bundle ImplTest with Impl so everything goes into one .c
#   - Drop FStar/Pulse/Prims modules (not needed at runtime)
#   - Impl Pulse functions become extern declarations (provided by hand-written C)
$(OUTPUT_DIR)/CLRS_Ch11_HashTable_ImplTest.c: $(OUTPUT_DIR)/CLRS_Ch11_HashTable_combined.krml
	$(call msg, "KRML", "CLRS_Ch11_HashTable_ImplTest")
	$(KRML_EXE) -skip-makefiles -skip-compilation \
	  -bundle 'CLRS.Ch11.HashTable.ImplTest=CLRS.Ch11.HashTable.Impl' \
	  -bundle 'FStar.*,Pulse.*,Prims,PulseCore.*,LowStar.*' \
	  -warn-error -9-2-15 \
	  -add-include '"krml/internal/compat.h"' \
	  -add-include '"CLRS_Ch11_HashTable_Impl.h"' \
	  -header $(PULSE_ROOT)/mk/krmlheader \
	  -tmpdir $(OUTPUT_DIR) \
	  $<

# Step 3: Compile extracted C + hand-written Impl C + main driver to executable
$(OUTPUT_DIR)/ht_test: $(OUTPUT_DIR)/CLRS_Ch11_HashTable_ImplTest.c CLRS_Ch11_HashTable_Impl.c main.c
	$(call msg, "CC", "ht_test")
	cc -Wall -Wno-parentheses -g \
	  -I $(KRML_DIST) -I $(KRML_HOME)/krmllib -I $(KRML_INCLUDE) -I $(OUTPUT_DIR) -I . \
	  $(OUTPUT_DIR)/CLRS_Ch11_HashTable_ImplTest.c \
	  CLRS_Ch11_HashTable_Impl.c main.c \
	  -o $@

# Step 4: Run the test executable
$(OUTPUT_DIR)/ht_test.out: $(OUTPUT_DIR)/ht_test
	$(call msg, "RUN", "ht_test")
	./$< > $@
	@cat $@

# Convenience targets
extract: $(OUTPUT_DIR)/CLRS_Ch11_HashTable_ImplTest.c
test: $(OUTPUT_DIR)/ht_test.out
