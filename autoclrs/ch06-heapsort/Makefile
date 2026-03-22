PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────────
KRML_ROOT  ?= ../../krml/karamel
KRML       ?= $(KRML_ROOT)/krml
KRMLLIB    ?= $(KRML_ROOT)/krmllib/dist/generic
KRML_INC   ?= $(KRML_ROOT)/include

KRML_FILES = $(OUTPUT_DIR)/CLRS_Ch06_Heap_Impl.krml \
             $(OUTPUT_DIR)/CLRS_Ch06_Heap_ImplTest.krml \
             $(OUTPUT_DIR)/Pulse_Lib_BoundedIntegers.krml

# Bundle all modules into a single C translation unit via krml
$(OUTPUT_DIR)/CLRS_Ch06_Heap_ImplTest.c: $(KRML_FILES)
	$(call msg, "KRML", "CLRS_Ch06_Heap_ImplTest")
	$(KRML) -skip-compilation -skip-linking -skip-makefiles \
	  -add-include '"krml/internal/compat.h"' \
	  -warn-error -2-9-11-15 \
	  -bundle 'CLRS.Ch06.Heap.ImplTest=CLRS.Ch06.Heap.*,Pulse.Lib.BoundedIntegers' \
	  -tmpdir $(OUTPUT_DIR) \
	  $(KRML_FILES)

# Compile extracted C + main driver into test executable
$(OUTPUT_DIR)/test_heapsort: $(OUTPUT_DIR)/CLRS_Ch06_Heap_ImplTest.c main.c
	$(call msg, "CC", "test_heapsort")
	$(CC) -O2 -I$(KRML_INC) -I$(KRMLLIB) -I$(OUTPUT_DIR) \
	  main.c $(OUTPUT_DIR)/CLRS_Ch06_Heap_ImplTest.c \
	  -o $@

# Run the test
$(OUTPUT_DIR)/test_heapsort.out: $(OUTPUT_DIR)/test_heapsort
	$(call msg, "RUN", "test_heapsort")
	$(OUTPUT_DIR)/test_heapsort | tee $@

.PHONY: extract test
extract: $(OUTPUT_DIR)/CLRS_Ch06_Heap_ImplTest.c
test: $(OUTPUT_DIR)/test_heapsort.out
