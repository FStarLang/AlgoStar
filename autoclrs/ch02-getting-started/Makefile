PULSE_ROOT ?= ../../pulse
OTHERFLAGS += --include ../common
include $(PULSE_ROOT)/mk/test.mk

# ============================================================================
# C extraction and testing via KaRaMeL
# ============================================================================

KRML_HOME ?= ../../krml/karamel
CSRC_DIR  = $(OUTPUT_DIR)/csrc

ISORT_KRML = $(OUTPUT_DIR)/CLRS_Ch02_InsertionSort_Impl.krml
MSORT_KRML = $(OUTPUT_DIR)/CLRS_Ch02_MergeSort_Impl.krml

# Step 1: Extract Pulse modules to .krml
$(ISORT_KRML): _cache/CLRS.Ch02.InsertionSort.Impl.fst.checked
	$(call msg, "EXTRACT", "CLRS_Ch02_InsertionSort_Impl.krml")
	$(FSTAR) CLRS.Ch02.InsertionSort.Impl.fst --codegen krml --extract 'CLRS.Ch02.InsertionSort.Impl'

$(MSORT_KRML): _cache/CLRS.Ch02.MergeSort.Impl.fst.checked
	$(call msg, "EXTRACT", "CLRS_Ch02_MergeSort_Impl.krml")
	$(FSTAR) CLRS.Ch02.MergeSort.Impl.fst --codegen krml --extract 'CLRS.Ch02.MergeSort.Impl'

# Step 2: KaRaMeL translates .krml to C
$(CSRC_DIR)/InsertionSort.c $(CSRC_DIR)/MergeSort.c &: $(ISORT_KRML) $(MSORT_KRML)
	$(call msg, "KRML", "InsertionSort.c MergeSort.c")
	@mkdir -p $(CSRC_DIR)
	$(KRML_HOME)/krml \
	  -tmpdir $(CSRC_DIR) \
	  -skip-compilation \
	  -warn-error -2-9-11-15-17 \
	  -bundle 'CLRS.Ch02.InsertionSort.Impl=CLRS.Ch02.InsertionSort.*,CLRS.Common.*[rename=InsertionSort]' \
	  -bundle 'CLRS.Ch02.MergeSort.Impl=CLRS.Ch02.MergeSort.*[rename=MergeSort]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  $(ISORT_KRML) $(MSORT_KRML) \
	  $(KRML_HOME)/krmllib/.extract/*.krml

# Step 3: Compile the C test
$(CSRC_DIR)/test_ch02: $(CSRC_DIR)/InsertionSort.c $(CSRC_DIR)/MergeSort.c test_main.c
	$(call msg, "CC", "test_ch02")
	gcc -o $@ \
	  -I$(KRML_HOME)/include \
	  -I$(KRML_HOME)/krmllib/dist/generic \
	  -I$(CSRC_DIR) \
	  test_main.c \
	  $(CSRC_DIR)/InsertionSort.c \
	  $(CSRC_DIR)/MergeSort.c \
	  $(KRML_HOME)/krmllib/c/prims.c \
	  $(KRML_HOME)/krmllib/c/fstar_int32.c \
	  -Wno-unused-variable

# Step 4: Run the test
$(CSRC_DIR)/test_ch02.out: $(CSRC_DIR)/test_ch02
	$(call msg, "RUN", "test_ch02")
	./$< | tee $@

.PHONY: extract test-c
extract: $(CSRC_DIR)/InsertionSort.c $(CSRC_DIR)/MergeSort.c
test-c: $(CSRC_DIR)/test_ch02.out
