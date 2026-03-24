PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk

# ========== C extraction and test targets for ImplTest ==========
CHAPTER_ID       = ch26

# Explicit .krml extraction
extract-krml: _cache/CLRS.Ch26.MaxFlow.ImplTest.fst.checked \
              _cache/CLRS.Ch26.MaxFlow.Impl.fst.checked
	$(call msg, "EXTRACT", "CLRS.Ch26.MaxFlow → krml")
	$(FSTAR) CLRS.Ch26.MaxFlow.ImplTest.fst --codegen krml \
	  --extract_module CLRS.Ch26.MaxFlow.ImplTest
	$(FSTAR) CLRS.Ch26.MaxFlow.Impl.fst --codegen krml \
	  --extract_module CLRS.Ch26.MaxFlow.Impl

KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_Impl.krml \
                    $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_ImplTest.krml
KRML_BUNDLE_FLAGS = -bundle CLRS.Ch26.MaxFlow.ImplTest=CLRS.Ch26.MaxFlow.*
KRML_WARN_FLAGS   = -warn-error -2-15
EXTRACT_C_FILES   = $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_ImplTest.c
EXTRA_LINK_LIBS   = $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a
CC_EXTRA_FLAGS    = -Wno-implicit-function-declaration
CC_EXTRA_INCLUDES = -include clrs_ch26_compat.h
TEST_MAIN         = test_main.c
TEST_EXE_NAME     = test_max_flow

include ../autoclrs.test.mk

