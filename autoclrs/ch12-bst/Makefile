PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test for pointer-based BST ────────────────────
CHAPTER_ID        = ch12

BST_KRML_FILES := \
  $(OUTPUT_DIR)/CLRS_Ch12_BST_TestMain.krml \
  $(OUTPUT_DIR)/CLRS_Ch12_BST_ImplTest.krml \
  $(OUTPUT_DIR)/CLRS_Ch12_BST_Impl.krml \
  $(OUTPUT_DIR)/FStar_Pervasives.krml \
  $(OUTPUT_DIR)/FStar_Pervasives_Native.krml

KRML_INPUT_FILES  = $(BST_KRML_FILES)
KRML_BUNDLE_FLAGS = -bundle 'CLRS.Ch12.BST.TestMain=CLRS.Ch12.BST.ImplTest,CLRS.Ch12.BST.Impl'
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch12_BST_TestMain.c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/c/prims.c \
                    $(KRML_HOME)/krmllib/c/fstar_int32.c
TEST_EXE_NAME     = bst_test

include ../autoclrs.test.mk
