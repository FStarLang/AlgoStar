PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
include $(PULSE_ROOT)/mk/test.mk
# Undo optimize_let_vc and fly_deps — they break proofs in
# TopologicalSort.Impl and TopologicalSort.Verified.fst
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --ext optimize_let_vc=false --ext fly_deps=false --include ../common

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch22
EXTRACT_DIR       = $(OUTPUT_DIR)/csrc

IMPLTEST_KRML = \
	$(OUTPUT_DIR)/CLRS_Ch22_ImplTestMain.krml \
	$(OUTPUT_DIR)/CLRS_Ch22_BFS_ImplTest.krml \
	$(OUTPUT_DIR)/CLRS_Ch22_DFS_ImplTest.krml \
	$(OUTPUT_DIR)/CLRS_Ch22_TopologicalSort_ImplTest.krml \
	$(OUTPUT_DIR)/CLRS_Ch22_BFS_Impl.krml \
	$(OUTPUT_DIR)/CLRS_Ch22_DFS_Impl.krml \
	$(OUTPUT_DIR)/CLRS_Ch22_TopologicalSort_Impl.krml \
	$(OUTPUT_DIR)/CLRS_Ch22_TopologicalSort_Impl_Defs.krml \
	$(OUTPUT_DIR)/CLRS_Ch22_Graph_Common.krml \
	$(OUTPUT_DIR)/CLRS_Ch22_TopologicalSort_Spec.krml

KRML_INPUT_FILES  = $(IMPLTEST_KRML)
KRML_BUNDLE_FLAGS = -bundle 'CLRS.Ch22.ImplTestMain=*'
KRML_WARN_FLAGS   = -warn-error -2 -warn-error -4 -warn-error -1 -warn-error -15 -warn-error -17 -warn-error -9
KRML_EXTRA_FLAGS  = -add-include '"ch22_support.h"'
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch22_ImplTestMain.c
CC_EXTRA_INCLUDES = -I .
TEST_EXE_NAME     = ch22_test

include ../autoclrs.test.mk

# Override: also depend on the support header
$(TEST_EXE): ch22_support.h
