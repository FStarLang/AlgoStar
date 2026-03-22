PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk

# ========== C extraction and test targets for ImplTest ==========

KRML_ROOT ?= ../../krml/karamel
KRML_BIN  ?= $(KRML_ROOT)/krml
KRML_INC   = $(KRML_ROOT)/include
KRML_DIST  = $(KRML_ROOT)/krmllib/dist/minimal
KRML_LIB   = $(KRML_ROOT)/krmllib/dist/generic/libkrmllib.a

# Step 1: extract ImplTest + Impl modules to .krml
# Uses a single F* invocation so the combined out.krml AND per-module krml files
# are produced. We pass both krml files to krml.
extract-krml: _cache/CLRS.Ch26.MaxFlow.ImplTest.fst.checked \
              _cache/CLRS.Ch26.MaxFlow.Impl.fst.checked
	$(call msg, "EXTRACT", "CLRS.Ch26.MaxFlow → krml")
	$(FSTAR) CLRS.Ch26.MaxFlow.ImplTest.fst --codegen krml \
	  --extract_module CLRS.Ch26.MaxFlow.ImplTest
	$(FSTAR) CLRS.Ch26.MaxFlow.Impl.fst --codegen krml \
	  --extract_module CLRS.Ch26.MaxFlow.Impl

# Step 2: run krml to produce C from .krml files.
# Bundle all CLRS.Ch26.MaxFlow modules into a single ImplTest C file.
extract-c: extract-krml
	$(call msg, "KRML", "CLRS.Ch26.MaxFlow.ImplTest → C")
	$(KRML_BIN) \
	  -skip-makefiles \
	  -skip-compilation \
	  -skip-linking \
	  -warn-error -2-15 \
	  -add-include '"krml/internal/compat.h"' \
	  -bundle CLRS.Ch26.MaxFlow.ImplTest=CLRS.Ch26.MaxFlow.* \
	  -tmpdir $(OUTPUT_DIR) \
	  $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_Impl.krml \
	  $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_ImplTest.krml

# Step 3: compile the extracted C + test harness
compile-test: extract-c
	$(call msg, "CC", "test_max_flow")
	$(CC) -o $(OUTPUT_DIR)/test_max_flow \
	  test_main.c $(OUTPUT_DIR)/CLRS_Ch26_MaxFlow_ImplTest.c \
	  -include clrs_ch26_compat.h \
	  -I$(OUTPUT_DIR) -I$(KRML_INC) -I$(KRML_DIST) \
	  -Wall -std=c11 -g -fwrapv \
	  -Wno-unused-parameter -Wno-unused-variable \
	  -Wno-parentheses -Wno-implicit-function-declaration \
	  $(KRML_LIB)

# Step 4: run the test
test: compile-test
	$(call msg, "RUN", "test_max_flow")
	$(OUTPUT_DIR)/test_max_flow

.PHONY: extract-krml extract-c compile-test test

