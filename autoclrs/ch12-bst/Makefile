PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
STAGE3     ?= 1
export STAGE3
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test for Chapter 12 BSTs ──────────────────────
CHAPTER_ID        = ch12
EXTRACT_DIR       = _output/c

# ── Pointer-based BST krml inputs ──────────────────────────────────
BST_KRML_FILES := \
  $(OUTPUT_DIR)/CLRS_Ch12_BST_TestMain.krml \
  $(OUTPUT_DIR)/CLRS_Ch12_BST_ImplTest.krml \
  $(OUTPUT_DIR)/CLRS_Ch12_BST_Impl.krml \
  $(OUTPUT_DIR)/FStar_Pervasives.krml \
  $(OUTPUT_DIR)/FStar_Pervasives_Native.krml

# ── Array-based BST krml inputs ───────────────────────────────────
BSTARRAY_KRML_FILES := \
  $(OUTPUT_DIR)/CLRS_Ch12_BSTArray_TestMain.krml \
  $(OUTPUT_DIR)/CLRS_Ch12_BSTArray_ImplTest.krml \
  $(OUTPUT_DIR)/CLRS_Ch12_BSTArray_Impl.krml

KRML_INPUT_FILES  = $(BST_KRML_FILES) $(BSTARRAY_KRML_FILES)
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch12.BST.TestMain=CLRS.Ch12.BST.ImplTest,CLRS.Ch12.BST.Impl' \
  -bundle 'CLRS.Ch12.BSTArray.TestMain=CLRS.Ch12.BSTArray.ImplTest,CLRS.Ch12.BSTArray.Impl' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch12_BST_TestMain.c \
                    $(EXTRACT_DIR)/CLRS_Ch12_BSTArray_TestMain.c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/c/prims.c \
                    $(KRML_HOME)/krmllib/c/fstar_int32.c
TEST_EXE_NAME     = bst_test

# Cancel Pulse's generic .krml -> .c pattern rules for our extract dir
$(EXTRACT_DIR)/%.krml:
	@true
$(EXTRACT_DIR)/%.c: $(EXTRACT_DIR)/%.krml
	@true

include ../autoclrs.test.mk
