PULSE_ROOT ?= ../../pulse
OTHERFLAGS += --ext optimize_let_vc=false --ext fly_deps=false
include $(PULSE_ROOT)/mk/test.mk

# ===== C extraction, compilation, and testing =====

KRML_HOME ?= ../../krml/karamel
KRML_EXE  ?= $(KRML_HOME)/krml

CSRC_DIR    = $(OUTPUT_DIR)/csrc
KRML_DIST   = $(KRML_HOME)/krmllib/dist/minimal
KRML_INCLUDE = $(KRML_HOME)/include

# Modules to extract to .krml
EXTRACT_KRML = \
  $(OUTPUT_DIR)/CLRS_Ch24_Run.krml \
  $(OUTPUT_DIR)/CLRS_Ch24_BellmanFord_Impl.krml \
  $(OUTPUT_DIR)/CLRS_Ch24_ShortestPath_Inf.krml \
  $(OUTPUT_DIR)/CLRS_Ch24_ShortestPath_Spec.krml \
  $(OUTPUT_DIR)/CLRS_Ch24_Dijkstra_Impl.krml \
  $(OUTPUT_DIR)/CLRS_Ch24_Dijkstra.krml

$(CSRC_DIR):
	mkdir -p $@

# Extract all .krml → single bundled .c
extract-c: $(EXTRACT_KRML) | $(CSRC_DIR)
	$(KRML_EXE) \
	  -skip-makefiles \
	  -skip-compilation \
	  -add-include '"krml/internal/compat.h"' \
	  -warn-error -1-2-5-7-9-11-15-17 \
	  -bundle 'CLRS.Ch24.Run=CLRS.*[rename=Ch24_SSSP]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -no-prefix CLRS.Ch24.Run \
	  -tmpdir $(CSRC_DIR) \
	  $(EXTRACT_KRML)
	@cp $(CSRC_DIR)/prims_shim.c $(CSRC_DIR)/prims_shim.c 2>/dev/null || \
	  printf '%s\n' \
	    '#include <stdint.h>' \
	    '#include <stdbool.h>' \
	    '#include <stdio.h>' \
	    '#include <stdlib.h>' \
	    '#include "krml/internal/compat.h"' \
	    'bool Prims_op_GreaterThanOrEqual(int32_t x, int32_t y) { return x >= y; }' \
	    'bool Prims_op_LessThanOrEqual(int32_t x, int32_t y) { return x <= y; }' \
	    'bool Prims_op_GreaterThan(int32_t x, int32_t y) { return x > y; }' \
	    'bool Prims_op_LessThan(int32_t x, int32_t y) { return x < y; }' \
	    'int32_t Prims_op_Addition(int32_t x, int32_t y) { RETURN_OR((int64_t)x + (int64_t)y); }' \
	    'int32_t Prims_op_Subtraction(int32_t x, int32_t y) { RETURN_OR((int64_t)x - (int64_t)y); }' \
	    'int32_t Prims_op_Multiply(int32_t x, int32_t y) { RETURN_OR((int64_t)x * (int64_t)y); }' \
	    > $(CSRC_DIR)/prims_shim.c

CC      ?= gcc
CFLAGS   = -std=c11 -Wall -Wno-unused-variable -Wno-parentheses \
           -Wno-implicit-function-declaration -g \
           -I$(CSRC_DIR) -I$(KRML_DIST) -I$(KRML_INCLUDE) \
           -DKRML_HOST_MALLOC=malloc -DKRML_HOST_CALLOC=calloc \
           -DKRML_HOST_FREE=free -DKRML_HOST_EXIT=exit \
           -DKRML_HOST_EPRINTF=eprintf -DKRML_HOST_PRINTF=printf

# Compile extracted C + main driver
$(CSRC_DIR)/test_ch24: extract-c main.c
	$(CC) $(CFLAGS) -o $@ \
	  main.c \
	  $(CSRC_DIR)/Ch24_SSSP.c \
	  $(CSRC_DIR)/krmlinit.c \
	  $(CSRC_DIR)/prims_shim.c

# Run the test
test-c: $(CSRC_DIR)/test_ch24
	$(CSRC_DIR)/test_ch24

.PHONY: extract-c test-c

