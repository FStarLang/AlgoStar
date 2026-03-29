PULSE_ROOT ?= ../../FStar/pulse
OTHERFLAGS += --ext optimize_let_vc=false --ext fly_deps=false
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch24
EXTRACT_DIR       = $(OUTPUT_DIR)/csrc

EXTRACT_KRML = \
  $(OUTPUT_DIR)/CLRS_Ch24_Run.krml \
  $(OUTPUT_DIR)/CLRS_Ch24_BellmanFord_Impl.krml \
  $(OUTPUT_DIR)/CLRS_Ch24_ShortestPath_Inf.krml \
  $(OUTPUT_DIR)/CLRS_Ch24_ShortestPath_Spec.krml \
  $(OUTPUT_DIR)/CLRS_Ch24_Dijkstra_Impl.krml \
  $(OUTPUT_DIR)/CLRS_Ch24_Dijkstra.krml

KRML_INPUT_FILES  = $(EXTRACT_KRML)
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch24.Run=CLRS.*[rename=Ch24_SSSP]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_WARN_FLAGS   = -warn-error -1-2-5-7-9-11-15-17
KRML_EXTRA_FLAGS  = -no-prefix CLRS.Ch24.Run
EXTRACT_C_FILES   = $(EXTRACT_DIR)/Ch24_SSSP.c

# Auto-generate prims_shim.c if needed
$(EXTRACT_DIR)/prims_shim.c: $(EXTRACT_C_FILES)
	@cp $(EXTRACT_DIR)/prims_shim.c $(EXTRACT_DIR)/prims_shim.c 2>/dev/null || \
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
	    > $(EXTRACT_DIR)/prims_shim.c

EXTRA_C_SOURCES   = $(EXTRACT_DIR)/krmlinit.c $(EXTRACT_DIR)/prims_shim.c
CC_EXTRA_FLAGS    = -Wno-implicit-function-declaration \
                    -DKRML_HOST_MALLOC=malloc -DKRML_HOST_CALLOC=calloc \
                    -DKRML_HOST_FREE=free -DKRML_HOST_EXIT=exit \
                    -DKRML_HOST_EPRINTF=eprintf -DKRML_HOST_PRINTF=printf
TEST_EXE_NAME     = test_ch24

include ../autoclrs.test.mk
