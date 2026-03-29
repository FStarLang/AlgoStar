PULSE_ROOT ?= ../../FStar/pulse

KRML_HOME  ?= ../../FStar/karamel
KRML_EXE  ?= $(KRML_HOME)/krml

include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ───────────────────────────────────────
CHAPTER_ID         = ch04

IMPL_MODULES = \
  CLRS.Ch04.BinarySearch.Impl \
  CLRS.Ch04.MatrixMultiply.Impl \
  CLRS.Ch04.MaxSubarray.Kadane

TEST_MODULES = \
  CLRS.Ch04.BinarySearch.ImplTest \
  CLRS.Ch04.MatrixMultiply.ImplTest \
  CLRS.Ch04.MaxSubarray.Kadane.ImplTest

ALL_EXTRACT_MODULES = $(IMPL_MODULES) $(TEST_MODULES)

BUNDLE_API = CLRS.Ch04.BinarySearch.ImplTest+CLRS.Ch04.MatrixMultiply.ImplTest+CLRS.Ch04.MaxSubarray.Kadane.ImplTest
BUNDLE_C_STEM = CLRS_Ch04_BinarySearch_ImplTest_CLRS_Ch04_MatrixMultiply_ImplTest_CLRS_Ch04_MaxSubarray_Kadane_ImplTest

# Per-module .krml extraction convenience (maps dotted names to underscored filenames)
$(OUTPUT_DIR)/%_krml_extracted: _cache/%.fst.checked
	$(call msg, "EXTRACT", $*)
	$(FSTAR) $< --codegen krml --extract_module $*
	@touch $@

define krml_rule
$(OUTPUT_DIR)/$(subst .,_,$(1)).krml: $(OUTPUT_DIR)/$(1)_krml_extracted
	@true
endef
$(foreach m,$(ALL_EXTRACT_MODULES),$(eval $(call krml_rule,$(m))))

KRML_INPUT_FILES  = $(patsubst %,$(OUTPUT_DIR)/$(subst .,_,%).krml,$(ALL_EXTRACT_MODULES))
KRML_BUNDLE_FLAGS = -bundle '$(BUNDLE_API)=CLRS.Ch04.*'
KRML_EXTRA_FLAGS  = -header=$(PULSE_ROOT)/mk/krmlheader
EXTRACT_C_FILES   = $(OUTPUT_DIR)/$(BUNDLE_C_STEM).c
EXTRA_LINK_LIBS   = $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a

include ../autoclrs.test.mk
