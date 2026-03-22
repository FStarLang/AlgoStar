PULSE_ROOT ?= ../../pulse
KRML_HOME ?= ../../krml/karamel
include $(PULSE_ROOT)/mk/test.mk

# ---------- C extraction and testing ----------

C_OUTPUT_DIR = $(OUTPUT_DIR)/c

EXTRACT_KRML_MODULES = \
  CLRS_Ch33_Segments_Impl \
  CLRS_Ch33_Segments_ImplTest \
  CLRS_Ch33_GrahamScan_Impl \
  CLRS_Ch33_GrahamScan_ImplTest \
  CLRS_Ch33_JarvisMarch_Impl \
  CLRS_Ch33_JarvisMarch_ImplTest

LOCAL_KRML_FILES = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(EXTRACT_KRML_MODULES))
KRMLLIB_KRML_FILES = $(wildcard $(KRML_HOME)/krmllib/.extract/*.krml)

BUNDLE_NAME = CLRS_Ch33_Segments_ImplTest_CLRS_Ch33_GrahamScan_ImplTest_CLRS_Ch33_JarvisMarch_ImplTest

extract_c: $(LOCAL_KRML_FILES)
	@mkdir -p $(C_OUTPUT_DIR)
	$(KRML_EXE) \
	  -tmpdir $(C_OUTPUT_DIR) \
	  -skip-compilation \
	  -warn-error -2-9-11-15-17 \
	  -bundle 'CLRS.Ch33.Segments.ImplTest+CLRS.Ch33.GrahamScan.ImplTest+CLRS.Ch33.JarvisMarch.ImplTest=CLRS.Ch33.*' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  $(LOCAL_KRML_FILES) \
	  $(KRMLLIB_KRML_FILES)

CFLAGS_CH33 = -std=c11 -g -fwrapv -Wall -Wextra \
  -Wno-unused-parameter -Wno-unused-variable -Wno-unused-but-set-variable \
  -Wno-parentheses \
  -I $(C_OUTPUT_DIR) \
  -I $(KRML_HOME)/include \
  -I $(KRML_HOME)/krmllib/dist/generic

test_c: extract_c
	$(CC) $(CFLAGS_CH33) \
	  -o $(C_OUTPUT_DIR)/ch33_test \
	  main.c \
	  $(C_OUTPUT_DIR)/$(BUNDLE_NAME).c \
	  $(C_OUTPUT_DIR)/C.c \
	  $(C_OUTPUT_DIR)/C_Failure.c \
	  $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a
	$(C_OUTPUT_DIR)/ch33_test
