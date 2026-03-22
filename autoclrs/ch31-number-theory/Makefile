PULSE_ROOT ?= ../../pulse
OTHERFLAGS += --include ../common
include $(PULSE_ROOT)/mk/test.mk

# --- C extraction and test targets ---

KRML_HOME ?= ../../krml/karamel

# Modules to extract to .krml
EXTRACT_MODULES = \
  CLRS.Ch31.GCD.ImplTest \
  CLRS.Ch31.GCD.Impl \
  CLRS.Ch31.GCD.Spec \
  CLRS.Ch31.GCD.Complexity \
  CLRS.Ch31.GCD.Lemmas \
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

KRML_FILES = $(foreach m,$(EXTRACT_MODULES),$(OUTPUT_DIR)/$(subst .,_,$m).krml)
BUNDLE_C = CLRS_Ch31_GCD_ImplTest_CLRS_Ch31_ModExp_ImplTest_CLRS_Ch31_ModExpLR_ImplTest
KRML_INC = -I $(KRML_HOME)/krmllib/dist/minimal -I $(KRML_HOME)/krmllib -I $(KRML_HOME)/include -I $(OUTPUT_DIR)

# Extract all modules to .krml, then run karamel to produce C
$(OUTPUT_DIR)/$(BUNDLE_C).c: $(KRML_FILES)
	$(call msg, "KRML", "$(BUNDLE_C).c")
	$(KRML_HOME)/krml \
	  -skip-makefiles -skip-linking -skip-compilation \
	  -tmpdir $(OUTPUT_DIR) \
	  -warn-error -2-1-15 \
	  -add-include '"krml/internal/compat.h"' \
	  -bundle 'CLRS.Ch31.GCD.ImplTest+CLRS.Ch31.ModExp.ImplTest+CLRS.Ch31.ModExpLR.ImplTest=CLRS.*' \
	  -bundle 'FStar.*' \
	  -bundle 'Pulse.*' \
	  -bundle 'PulseCore.*' \
	  -bundle 'Prims' \
	  $(KRML_FILES) \
	  $(KRML_HOME)/krmllib/.extract/*.krml

# Compile and link the test executable
$(OUTPUT_DIR)/ch31_test: $(OUTPUT_DIR)/$(BUNDLE_C).c main.c
	$(call msg, "CC", "ch31_test")
	cc -o $@ \
	  main.c \
	  $(OUTPUT_DIR)/$(BUNDLE_C).c \
	  $(KRML_HOME)/krmllib/dist/generic/prims.c \
	  $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c \
	  $(KRML_INC) \
	  -std=c11 -Wno-implicit-function-declaration

# Run the test
$(OUTPUT_DIR)/ch31_test.out: $(OUTPUT_DIR)/ch31_test
	$(call msg, "RUN", "ch31_test")
	$(OUTPUT_DIR)/ch31_test | tee $@

extract: $(OUTPUT_DIR)/$(BUNDLE_C).c
test: $(OUTPUT_DIR)/ch31_test.out
