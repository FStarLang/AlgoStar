PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk

# ============================================================
# C extraction and test for pointer-based BST (ImplTest)
# ============================================================

KRML_HOME ?= ../../krml/karamel
KRMLLIB   := $(KRML_HOME)/krmllib

# Modules to extract to .krml
BST_KRML_FILES := \
  $(OUTPUT_DIR)/CLRS_Ch12_BST_TestMain.krml \
  $(OUTPUT_DIR)/CLRS_Ch12_BST_ImplTest.krml \
  $(OUTPUT_DIR)/CLRS_Ch12_BST_Impl.krml \
  $(OUTPUT_DIR)/FStar_Pervasives.krml \
  $(OUTPUT_DIR)/FStar_Pervasives_Native.krml

# C compiler flags for krmllib
CFLAGS_KRML := \
  -I $(KRMLLIB)/dist/minimal \
  -I $(KRMLLIB)/dist/generic \
  -I $(KRMLLIB) \
  -I $(KRML_HOME)/include \
  -I $(OUTPUT_DIR) \
  -Wall -g -fwrapv \
  -D_BSD_SOURCE -D_DEFAULT_SOURCE \
  -Wno-parentheses -std=c11

# Step 1: run krml to produce a single bundled C file
$(OUTPUT_DIR)/CLRS_Ch12_BST_TestMain.c: $(BST_KRML_FILES)
	$(call msg, "KRML", "BST TestMain")
	$(KRML_HOME)/krml \
	  -skip-makefiles -skip-compilation \
	  -add-include '"krml/internal/compat.h"' \
	  -bundle 'CLRS.Ch12.BST.TestMain=CLRS.Ch12.BST.ImplTest,CLRS.Ch12.BST.Impl' \
	  -tmpdir $(OUTPUT_DIR) \
	  $(BST_KRML_FILES)

# Step 2: compile the generated C, krmllib helpers, and main driver
$(OUTPUT_DIR)/CLRS_Ch12_BST_TestMain.o: $(OUTPUT_DIR)/CLRS_Ch12_BST_TestMain.c
	$(call msg, "CC", "CLRS_Ch12_BST_TestMain.c")
	cc $(CFLAGS_KRML) -c $< -o $@

$(OUTPUT_DIR)/prims.o: $(OUTPUT_DIR)/CLRS_Ch12_BST_TestMain.c
	$(call msg, "CC", "prims.c")
	cc $(CFLAGS_KRML) -c $(KRMLLIB)/c/prims.c -o $@

$(OUTPUT_DIR)/fstar_int32.o: $(OUTPUT_DIR)/CLRS_Ch12_BST_TestMain.c
	$(call msg, "CC", "fstar_int32.c")
	cc $(CFLAGS_KRML) -c $(KRMLLIB)/c/fstar_int32.c -o $@

$(OUTPUT_DIR)/main.o: main.c $(OUTPUT_DIR)/CLRS_Ch12_BST_TestMain.c
	$(call msg, "CC", "main.c")
	cc $(CFLAGS_KRML) -c main.c -o $@

# Step 3: link into test executable
$(OUTPUT_DIR)/bst_test: $(OUTPUT_DIR)/main.o $(OUTPUT_DIR)/CLRS_Ch12_BST_TestMain.o $(OUTPUT_DIR)/prims.o $(OUTPUT_DIR)/fstar_int32.o
	$(call msg, "LINK", "bst_test")
	cc $^ -o $@

# Step 4: run the test
$(OUTPUT_DIR)/bst_test.out: $(OUTPUT_DIR)/bst_test
	$(call msg, "RUN", "bst_test")
	$< | tee $@

# Convenience targets
.PHONY: extract-bst test-bst
extract-bst: $(OUTPUT_DIR)/CLRS_Ch12_BST_TestMain.c
test-bst: $(OUTPUT_DIR)/bst_test.out
