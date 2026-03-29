PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
KRML_EXE   ?= $(KRML_HOME)/krml
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch16
EXTRACT_DIR       = _output/c_extract

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

KRML_INPUT_FILES  = $(addprefix $(OUTPUT_DIR)/,$(addsuffix .krml,$(KRML_MODULES)))
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch16.ActivitySelection.ImplTest=CLRS.Ch16.ActivitySelection.*' \
  -bundle 'CLRS.Ch16.Huffman.ImplTest=CLRS.Ch16.Huffman.*,Pulse.Lib.PriorityQueue,Pulse.Lib.ResizableVec,Pulse.Lib.TotalOrder,Pulse.Lib.Vec,Pulse.Lib.Box' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_WARN_FLAGS   = -warn-error -2-9-11-15-17-18
KRML_EXTRA_INPUTS = $(KRML_HOME)/krmllib/.extract/*.krml

# KaRaMeL produces multiple .c files; the Activity one is the primary target
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch16_ActivitySelection_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch16_Huffman_ImplTest.c \
                    $(EXTRACT_DIR)/FStar_Pulse_PulseCore_Prims.c \
                    $(EXTRACT_DIR)/krmlinit.c
EXTRA_C_SOURCES   = prims_stubs.c
CC_EXTRA_FLAGS    = -Wno-unused-but-set-variable
CC_EXTRA_INCLUDES = -I $(EXTRACT_DIR)/internal

include ../autoclrs.test.mk
