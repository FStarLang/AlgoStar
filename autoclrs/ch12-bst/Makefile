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

# ── Snapshot: self-contained C directory ─────────────────────────────
SNAPSHOT_DIR      = snapshot
SNAPSHOT_KRMLLIB  = $(SNAPSHOT_DIR)/krmllib

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES)
	@echo "  [SNAPSHOT] populating $(SNAPSHOT_DIR)"
	@mkdir -p $(SNAPSHOT_DIR)/internal
	@mkdir -p $(SNAPSHOT_KRMLLIB)/include/krml/internal
	@mkdir -p $(SNAPSHOT_KRMLLIB)/include/krml
	@mkdir -p $(SNAPSHOT_KRMLLIB)/dist/minimal
	@mkdir -p $(SNAPSHOT_KRMLLIB)/dist/generic
	@mkdir -p $(SNAPSHOT_KRMLLIB)/c
	@# Generated C files
	@cp $(EXTRACT_DIR)/CLRS_Ch12_BST_TestMain.c      $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch12_BST_TestMain.h      $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch12_BSTArray_TestMain.c  $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch12_BSTArray_TestMain.h  $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/internal/*.h                   $(SNAPSHOT_DIR)/internal/
	@# krmllib headers
	@cp $(KRML_HOME)/include/krmllib.h                     $(SNAPSHOT_KRMLLIB)/include/
	@cp $(KRML_HOME)/include/krml/internal/*.h             $(SNAPSHOT_KRMLLIB)/include/krml/internal/
	@cp $(KRML_HOME)/include/krml/lowstar_endianness.h     $(SNAPSHOT_KRMLLIB)/include/krml/
	@cp $(KRML_HOME)/include/krml/fstar_int.h              $(SNAPSHOT_KRMLLIB)/include/krml/
	@# krmllib dist headers
	@cp $(KRML_HOME)/krmllib/dist/minimal/*.h              $(SNAPSHOT_KRMLLIB)/dist/minimal/
	@cp $(KRML_HOME)/krmllib/dist/generic/Prims.h          $(SNAPSHOT_KRMLLIB)/dist/generic/
	@cp $(KRML_HOME)/krmllib/dist/generic/FStar_Int32.h    $(SNAPSHOT_KRMLLIB)/dist/generic/
	@# krmllib runtime C files
	@cp $(KRML_HOME)/krmllib/c/prims.c                     $(SNAPSHOT_KRMLLIB)/c/
	@cp $(KRML_HOME)/krmllib/c/fstar_int32.c               $(SNAPSHOT_KRMLLIB)/c/
	@echo "  [SNAPSHOT] done — build with: make -C $(SNAPSHOT_DIR) run"
