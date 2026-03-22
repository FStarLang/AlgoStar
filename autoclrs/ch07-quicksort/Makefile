PULSE_ROOT ?= ../../pulse
OTHERFLAGS += --include ../common
include $(PULSE_ROOT)/mk/test.mk

# ========== C extraction and test targets ==========

KRML_HOME ?= ../../krml/karamel
KRML_BIN  ?= $(KRML_HOME)/krml
KRML_DIST  = $(KRML_HOME)/krmllib/dist/generic
KRML_INC   = $(KRML_HOME)/include
C_DIR      = _output/c

# .krml files needed for extraction (prerequisites come from .depend + test.mk rules)
KRML_FILES = _output/CLRS_Ch07_Quicksort_ImplTest.krml \
             _output/CLRS_Ch07_Quicksort_Impl.krml \
             _output/CLRS_Ch07_Partition_Impl.krml

# Step 1+2: Extract to .krml then translate to C via karamel.
# Use -library for Partition.Impl to work around a karamel bug in
# remove_unused_parameters when all three modules are processed together.
.PHONY: extract-c
extract-c: $(KRML_FILES)
	$(call msg, "KRML", "Translating to C")
	@mkdir -p $(C_DIR)
	$(KRML_BIN) -skip-makefiles -skip-compilation -skip-linking \
	  -warn-error -2-15 \
	  -add-include '"krml/internal/compat.h"' \
	  -library CLRS.Ch07.Partition.Impl \
	  -tmpdir $(C_DIR) \
	  $(KRML_FILES)

# Step 3: Compile extracted C + hand-written partition + main driver
CC_FLAGS = -Wall -Wno-parentheses -Wno-unused-variable -g -std=c11 \
           -I $(KRML_INC) -I $(KRML_DIST) -I $(C_DIR)

$(C_DIR)/quicksort_test.exe: extract-c main.c CLRS_Ch07_Partition_Impl.c fstar_support.c
	$(call msg, "CC", "quicksort_test.exe")
	$(CC) $(CC_FLAGS) -o $@ \
	  $(C_DIR)/CLRS_Ch07_Quicksort_Impl.c \
	  $(C_DIR)/CLRS_Ch07_Quicksort_ImplTest.c \
	  CLRS_Ch07_Partition_Impl.c \
	  fstar_support.c \
	  main.c \
	  $(KRML_DIST)/prims.c

.PHONY: compile-c
compile-c: $(C_DIR)/quicksort_test.exe

# Step 4: Run the test
$(C_DIR)/quicksort_test.out: $(C_DIR)/quicksort_test.exe
	$(call msg, "RUN", "quicksort_test")
	./$< > $@

.PHONY: test-c
test-c: $(C_DIR)/quicksort_test.out
	@cat $<
	@grep -q "tests passed" $< && echo "All tests passed!" || (echo "SOME TESTS FAILED"; exit 1)
