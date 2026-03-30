PULSE_ROOT ?= ../../FStar/pulse
STAGE3     ?= 1
KRML_HOME  ?= ../../FStar/karamel
include $(PULSE_ROOT)/mk/test.mk

# ========== C extraction and test targets for ImplTest ==========
CHAPTER_ID       = ch26

KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_ImplTest.krml \
                    $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_Impl.krml
KRML_BUNDLE_FLAGS = -bundle CLRS.Ch26.MaxFlow.ImplTest=CLRS.Ch26.MaxFlow.*
KRML_WARN_FLAGS   = -warn-error -2-9-11-15-17
EXTRACT_C_FILES   = $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_ImplTest.c
EXTRA_LINK_LIBS   = $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a
CC_EXTRA_INCLUDES = -include clrs_ch26_compat.h
TEST_MAIN         = test_main.c
TEST_EXE_NAME     = test_max_flow

include ../autoclrs.test.mk

