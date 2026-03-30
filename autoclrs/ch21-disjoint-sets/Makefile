PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
STAGE3     ?= 1
export STAGE3
OTHERFLAGS += --include ../common
include $(PULSE_ROOT)/mk/test.mk

# ========== C extraction and test targets ==========
CHAPTER_ID       = ch21

# Explicit .krml extraction rules (these modules need manual extraction)
$(OUTPUT_DIR)/CLRS_Ch21_UnionFind_ImplTest.krml: _cache/CLRS.Ch21.UnionFind.ImplTest.fst.checked
	$(call msg, "EXTRACT", "CLRS.Ch21.UnionFind.ImplTest")
	$(FSTAR) $< --codegen krml --extract_module CLRS.Ch21.UnionFind.ImplTest

$(OUTPUT_DIR)/CLRS_Ch21_UnionFind_Impl.krml: _cache/CLRS.Ch21.UnionFind.Impl.fst.checked
	$(call msg, "EXTRACT", "CLRS.Ch21.UnionFind.Impl")
	$(FSTAR) $< --codegen krml --extract_module CLRS.Ch21.UnionFind.Impl

KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch21_UnionFind_ImplTest.krml \
                    $(OUTPUT_DIR)/CLRS_Ch21_UnionFind_Impl.krml
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch21.UnionFind.ImplTest=CLRS.Ch21.UnionFind.*' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,C'
KRML_WARN_FLAGS   = -warn-error '-2-9-11-15-17'
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch21_UnionFind_ImplTest.c
KRML_EXTRA_INPUTS = $(wildcard $(KRML_HOME)/krmllib/.extract/*.krml)
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/c.c
TEST_EXE_NAME     = test_union_find

include ../autoclrs.test.mk
