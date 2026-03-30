PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch33
EXTRACT_DIR       = $(OUTPUT_DIR)/c

EXTRACT_KRML_MODULES = \
  CLRS_Ch33_Segments_Impl \
  CLRS_Ch33_Segments_ImplTest \
  CLRS_Ch33_GrahamScan_Impl \
  CLRS_Ch33_GrahamScan_ImplTest \
  CLRS_Ch33_JarvisMarch_Impl \
  CLRS_Ch33_JarvisMarch_ImplTest

KRML_INPUT_FILES  = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(EXTRACT_KRML_MODULES))
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch33.Segments.ImplTest+CLRS.Ch33.GrahamScan.ImplTest+CLRS.Ch33.JarvisMarch.ImplTest=CLRS.Ch33.*' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_EXTRA_INPUTS = $(wildcard $(KRML_HOME)/krmllib/.extract/*.krml)

BUNDLE_NAME       = CLRS_Ch33_Segments_ImplTest_CLRS_Ch33_GrahamScan_ImplTest_CLRS_Ch33_JarvisMarch_ImplTest
EXTRACT_C_FILES   = $(EXTRACT_DIR)/$(BUNDLE_NAME).c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c
EXTRA_LINK_LIBS   = -Wl,--gc-sections
CC_EXTRA_FLAGS    = -Wextra -Wno-unused-but-set-variable -ffunction-sections -fdata-sections

include ../autoclrs.test.mk
