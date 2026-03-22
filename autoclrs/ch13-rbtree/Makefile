PULSE_ROOT ?= ../../pulse
KRML_HOME ?= ../../krml/karamel
KRML_EXE  ?= $(KRML_HOME)/krml

include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────

KRML_INCLUDES = \
  -I $(KRML_HOME)/include \
  -I $(KRML_HOME)/krmllib/dist/minimal \
  -I $(KRML_HOME)/krmllib/dist/generic \
  -I $(OUTPUT_DIR)

KRML_RUNTIME_C = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                 $(KRML_HOME)/krmllib/c/fstar_int32.c

# Extra krml prerequisites for bundled extraction
KRML_DEPS = $(addprefix $(OUTPUT_DIR)/, \
  CLRS_Ch13_RBTree_ImplTest.krml \
  CLRS_Ch13_RBTree_Impl.krml \
  CLRS_Ch13_RBTree_Spec.krml \
  FStar_Pervasives_Native.krml \
  FStar_Pervasives.krml)

# Override the generic %.c rule for our bundled extraction
$(OUTPUT_DIR)/CLRS_Ch13_RBTree_Main.c: $(OUTPUT_DIR)/CLRS_Ch13_RBTree_Main.krml $(KRML_DEPS)
	$(call msg, "KRML", CLRS_Ch13_RBTree_Main)
	$(KRML_EXE) -skip-makefiles -skip-compilation \
	  -add-include '"krml/internal/compat.h"' \
	  -warn-error -15-20 \
	  -bundle 'CLRS.Ch13.RBTree.Main=CLRS.Ch13.RBTree.*' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  $+ -tmpdir $(OUTPUT_DIR)

$(OUTPUT_DIR)/test_rbtree: $(OUTPUT_DIR)/CLRS_Ch13_RBTree_Main.c test_main.c
	$(call msg, "CC", test_rbtree)
	gcc -std=c11 -Wno-parentheses -g \
	  $(KRML_INCLUDES) \
	  $(OUTPUT_DIR)/CLRS_Ch13_RBTree_Main.c \
	  $(KRML_RUNTIME_C) \
	  test_main.c \
	  -o $@

$(OUTPUT_DIR)/test_rbtree.out: $(OUTPUT_DIR)/test_rbtree
	$(call msg, "RUN", test_rbtree)
	./$< > $@ 2>&1
	cat $@

.PHONY: extract-c test-c
extract-c: $(OUTPUT_DIR)/CLRS_Ch13_RBTree_Main.c
test-c: $(OUTPUT_DIR)/test_rbtree.out
