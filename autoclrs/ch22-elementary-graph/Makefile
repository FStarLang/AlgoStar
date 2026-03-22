PULSE_ROOT ?= ../../pulse
KRML_HOME ?= ../../krml/karamel
include $(PULSE_ROOT)/mk/test.mk
# Undo optimize_let_vc and fly_deps — they break proofs in
# TopologicalSort.Impl and TopologicalSort.Verified.fst
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --ext optimize_let_vc=false --ext fly_deps=false --include ../common

# ---- C extraction and test targets ----

CSRC_DIR = $(OUTPUT_DIR)/csrc

# krml files needed for extraction (wrapper + tests + implementations)
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

CC_FLAGS = \
	-I $(KRML_HOME)/krmllib/dist/minimal \
	-I $(KRML_HOME)/krmllib \
	-I $(KRML_HOME)/include \
	-I $(CSRC_DIR) \
	-I . \
	-Wall -Wno-parentheses -std=c11 -g -fwrapv \
	-D_BSD_SOURCE -D_DEFAULT_SOURCE

# Extract to C via krml: bundle all CLRS modules into one translation unit
$(CSRC_DIR)/CLRS_Ch22_ImplTestMain.c: $(IMPLTEST_KRML)
	$(call msg, "KRML", "Ch22 ImplTest")
	mkdir -p $(CSRC_DIR)
	$(KRML_EXE) \
	  -skip-makefiles -skip-linking -skip-compilation \
	  -tmpdir $(CSRC_DIR) \
	  -bundle 'CLRS.Ch22.ImplTestMain=*' \
	  -add-include '"krml/internal/compat.h"' \
	  -add-include '"ch22_support.h"' \
	  -warn-error -2 -warn-error -4 -warn-error -1 -warn-error -15 -warn-error -17 -warn-error -9 \
	  $+

# Compile the test executable
$(CSRC_DIR)/ch22_test: $(CSRC_DIR)/CLRS_Ch22_ImplTestMain.c main.c ch22_support.h
	$(call msg, "CC", "ch22_test")
	$(CC) $(CC_FLAGS) -o $@ main.c $(CSRC_DIR)/CLRS_Ch22_ImplTestMain.c

# Run the test
$(CSRC_DIR)/ch22_test.out: $(CSRC_DIR)/ch22_test
	$(call msg, "RUN", "ch22_test")
	./$< > $@
	cat $@

.PHONY: extract test
extract: $(CSRC_DIR)/CLRS_Ch22_ImplTestMain.c
test: $(CSRC_DIR)/ch22_test.out
