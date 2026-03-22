PULSE_ROOT ?= ../../pulse

KRML_HOME ?= ../../krml/karamel
KRML_EXE  ?= $(KRML_HOME)/krml

include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ───────────────────────────────────────

# Modules whose implementations are extracted to C
IMPL_MODULES = \
  CLRS.Ch04.BinarySearch.Impl \
  CLRS.Ch04.MatrixMultiply.Impl \
  CLRS.Ch04.MaxSubarray.Kadane

# Test modules that exercise the implementations
TEST_MODULES = \
  CLRS.Ch04.BinarySearch.ImplTest \
  CLRS.Ch04.MatrixMultiply.ImplTest \
  CLRS.Ch04.MaxSubarray.Kadane.ImplTest

ALL_EXTRACT_MODULES = $(IMPL_MODULES) $(TEST_MODULES)
KRML_FILES = $(patsubst %,$(OUTPUT_DIR)/$(subst .,_,%).krml,$(ALL_EXTRACT_MODULES))

# Bundle name: the three ImplTest modules form the public API
BUNDLE_API = CLRS.Ch04.BinarySearch.ImplTest+CLRS.Ch04.MatrixMultiply.ImplTest+CLRS.Ch04.MaxSubarray.Kadane.ImplTest
BUNDLE_C_STEM = CLRS_Ch04_BinarySearch_ImplTest_CLRS_Ch04_MatrixMultiply_ImplTest_CLRS_Ch04_MaxSubarray_Kadane_ImplTest
BUNDLE_C = $(OUTPUT_DIR)/$(BUNDLE_C_STEM).c
BUNDLE_O = $(OUTPUT_DIR)/$(BUNDLE_C_STEM).o
MAIN_O   = $(OUTPUT_DIR)/main.o
TEST_EXE = $(OUTPUT_DIR)/ch04_tests

KRML_INCLUDE = -I $(KRML_HOME)/krmllib/dist/minimal \
               -I $(KRML_HOME)/krmllib \
               -I $(KRML_HOME)/include \
               -I $(OUTPUT_DIR)
CC_FLAGS = -Wall -Wextra -Werror -std=c11 -g -fwrapv \
           -D_BSD_SOURCE -D_DEFAULT_SOURCE \
           -Wno-unused-parameter -Wno-unused-variable \
           -Wno-unknown-warning-option

# Step 1: Extract F* modules to .krml
$(OUTPUT_DIR)/%_krml_extracted: _cache/%.fst.checked
	$(call msg, "EXTRACT", $*)
	$(FSTAR) $< --codegen krml --extract_module $*
	@touch $@

# Convenience: map dotted module names to underscored .krml filenames
define krml_rule
$(OUTPUT_DIR)/$(subst .,_,$(1)).krml: $(OUTPUT_DIR)/$(1)_krml_extracted
	@true
endef
$(foreach m,$(ALL_EXTRACT_MODULES),$(eval $(call krml_rule,$(m))))

# Step 2: Run KaRaMeL on all .krml files to produce bundled C
$(BUNDLE_C): $(foreach m,$(ALL_EXTRACT_MODULES),$(OUTPUT_DIR)/$(subst .,_,$(m)).krml)
	$(call msg, "KRML", "$(BUNDLE_C_STEM)")
	$(KRML_EXE) \
	  -skip-makefiles \
	  -skip-linking \
	  -skip-compilation \
	  -header=$(PULSE_ROOT)/mk/krmlheader \
	  -bundle '$(BUNDLE_API)=CLRS.Ch04.*' \
	  -add-include '"krml/internal/compat.h"' \
	  -tmpdir $(OUTPUT_DIR) \
	  $^

# Step 3: Compile the extracted C code
$(BUNDLE_O): $(BUNDLE_C)
	$(call msg, "CC", "$(BUNDLE_C_STEM)")
	cc $(CC_FLAGS) $(KRML_INCLUDE) -c $< -o $@

# Step 4: Compile the test driver
$(MAIN_O): main.c $(BUNDLE_C)
	$(call msg, "CC", "main")
	cc $(CC_FLAGS) $(KRML_INCLUDE) -c $< -o $@

KRML_LIB = $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a

# Step 5: Link the test executable
$(TEST_EXE): $(BUNDLE_O) $(MAIN_O) $(KRML_LIB)
	$(call msg, "LINK", "ch04_tests")
	cc $(CC_FLAGS) -o $@ $(BUNDLE_O) $(MAIN_O) $(KRML_LIB)

# Step 6: Run the tests
$(OUTPUT_DIR)/ch04_tests.out: $(TEST_EXE)
	$(call msg, "RUN", "ch04_tests")
	./$(TEST_EXE) | tee $@

.PHONY: extract test
extract: $(BUNDLE_C)
test: $(OUTPUT_DIR)/ch04_tests.out
