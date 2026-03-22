PULSE_ROOT ?= ../../pulse
KRML_HOME  ?= ../../krml/karamel
KRML_EXE   ?= $(KRML_HOME)/krml
include $(PULSE_ROOT)/mk/test.mk

# ============================================================================
# C extraction and test targets for ImplTest files
# ============================================================================

EXTRACT_DIR = _output/c_extract

# Modules to extract to .krml
KRML_MODULES = \
  CLRS_Ch16_ActivitySelection_ImplTest \
  CLRS_Ch16_ActivitySelection_Impl \
  CLRS_Ch16_Huffman_ImplTest \
  CLRS_Ch16_Huffman_Impl \
  CLRS_Ch16_Huffman_Defs \
  CLRS_Ch16_Huffman_PQForest \
  Pulse_Lib_PriorityQueue \
  Pulse_Lib_ResizableVec \
  Pulse_Lib_TotalOrder \
  Pulse_Lib_Vec \
  Pulse_Lib_Box

KRML_FILES = $(addprefix $(OUTPUT_DIR)/,$(addsuffix .krml,$(KRML_MODULES)))

KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch16.ActivitySelection.ImplTest=CLRS.Ch16.ActivitySelection.*' \
  -bundle 'CLRS.Ch16.Huffman.ImplTest=CLRS.Ch16.Huffman.*,Pulse.Lib.PriorityQueue,Pulse.Lib.ResizableVec,Pulse.Lib.TotalOrder,Pulse.Lib.Vec,Pulse.Lib.Box' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'

KRML_WARN_FLAGS = -warn-error -2-9-11-15-17-18

CC_INCLUDES = \
  -I $(KRML_HOME)/include \
  -I $(KRML_HOME)/krmllib/dist/generic \
  -I $(EXTRACT_DIR) \
  -I $(EXTRACT_DIR)/internal

CC_WARN = -Wno-unused-variable -Wno-unused-but-set-variable

# Step 1: Extract all modules to .krml (uses rules from test.mk)
extract-krml: $(KRML_FILES)

# Step 2: Run KaRaMeL to produce C
$(EXTRACT_DIR)/CLRS_Ch16_ActivitySelection_ImplTest.c: $(KRML_FILES)
	@mkdir -p $(EXTRACT_DIR)
	$(KRML_EXE) -tmpdir $(EXTRACT_DIR) -skip-compilation \
	  $(KRML_WARN_FLAGS) $(KRML_BUNDLE_FLAGS) \
	  $(KRML_FILES) $(KRML_HOME)/krmllib/.extract/*.krml

extract-c: $(EXTRACT_DIR)/CLRS_Ch16_ActivitySelection_ImplTest.c

# Step 3: Compile C and link
$(EXTRACT_DIR)/test_ch16: $(EXTRACT_DIR)/CLRS_Ch16_ActivitySelection_ImplTest.c prims_stubs.c main.c
	cc $(CC_INCLUDES) $(CC_WARN) -c $(EXTRACT_DIR)/CLRS_Ch16_ActivitySelection_ImplTest.c -o $(EXTRACT_DIR)/CLRS_Ch16_ActivitySelection_ImplTest.o
	cc $(CC_INCLUDES) $(CC_WARN) -c $(EXTRACT_DIR)/CLRS_Ch16_Huffman_ImplTest.c -o $(EXTRACT_DIR)/CLRS_Ch16_Huffman_ImplTest.o
	cc $(CC_INCLUDES) $(CC_WARN) -c $(EXTRACT_DIR)/FStar_Pulse_PulseCore_Prims.c -o $(EXTRACT_DIR)/FStar_Pulse_PulseCore_Prims.o
	cc $(CC_INCLUDES) $(CC_WARN) -c $(EXTRACT_DIR)/krmlinit.c -o $(EXTRACT_DIR)/krmlinit.o
	cc $(CC_INCLUDES) $(CC_WARN) -c prims_stubs.c -o $(EXTRACT_DIR)/prims_stubs.o
	cc $(CC_INCLUDES) $(CC_WARN) -c main.c -o $(EXTRACT_DIR)/main.o
	cc -o $@ $(EXTRACT_DIR)/CLRS_Ch16_ActivitySelection_ImplTest.o \
	  $(EXTRACT_DIR)/CLRS_Ch16_Huffman_ImplTest.o \
	  $(EXTRACT_DIR)/FStar_Pulse_PulseCore_Prims.o \
	  $(EXTRACT_DIR)/krmlinit.o \
	  $(EXTRACT_DIR)/prims_stubs.o \
	  $(EXTRACT_DIR)/main.o

build-test: $(EXTRACT_DIR)/test_ch16

# Step 4: Run the test
$(EXTRACT_DIR)/test_ch16.out: $(EXTRACT_DIR)/test_ch16
	$(EXTRACT_DIR)/test_ch16 | tee $@

test-c: $(EXTRACT_DIR)/test_ch16.out

.PHONY: extract-krml extract-c build-test test-c
