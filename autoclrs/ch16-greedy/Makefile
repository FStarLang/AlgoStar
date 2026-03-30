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
KRML_EXTRA_FLAGS  = -add-include '"fstar_support.h"'

# krmllib .krml files for FStar standard library types (option, order, seq).
# These are not shipped pre-built in fstar2; extract them on demand.
KRMLLIB_EXTRACT   = $(KRML_HOME)/krmllib/.extract
KRMLLIB_KRML      = $(KRMLLIB_EXTRACT)/FStar_Pervasives_Native.krml \
                    $(KRMLLIB_EXTRACT)/FStar_Order.krml \
                    $(KRMLLIB_EXTRACT)/FStar_Seq_Base.krml
FSTAR_ULIB        = $(shell dirname $$(readlink -f $(FSTAR_EXE)))/../lib/fstar/ulib

$(KRMLLIB_EXTRACT)/FStar_Pervasives_Native.krml: | $(KRMLLIB_EXTRACT)
	$(FSTAR_EXE) --no_cmi --odir $(KRMLLIB_EXTRACT) --codegen krml \
	  --extract_module FStar.Pervasives.Native \
	  $(FSTAR_ULIB)/FStar.Pervasives.Native.fst

$(KRMLLIB_EXTRACT)/FStar_Order.krml: | $(KRMLLIB_EXTRACT)
	$(FSTAR_EXE) --no_cmi --odir $(KRMLLIB_EXTRACT) --codegen krml \
	  --extract_module FStar.Order \
	  $(FSTAR_ULIB)/FStar.Order.fst

$(KRMLLIB_EXTRACT)/FStar_Seq_Base.krml: | $(KRMLLIB_EXTRACT)
	$(FSTAR_EXE) --no_cmi --odir $(KRMLLIB_EXTRACT) --codegen krml \
	  --extract_module FStar.Seq.Base \
	  $(FSTAR_ULIB)/FStar.Seq.Base.fst

$(KRMLLIB_EXTRACT):
	mkdir -p $@

KRML_EXTRA_INPUTS = $(KRMLLIB_KRML)

# KaRaMeL produces multiple .c files
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch16_ActivitySelection_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch16_Huffman_ImplTest.c \
                    $(EXTRACT_DIR)/FStar_Pulse_PulseCore_Prims.c
# Note: CLRS.Ch16.Huffman.Codec.ImplTest is NOT extracted because
# Codec.Impl functions (decode_impl, encode_impl, free_htree) take
# HSpec.htree as a non-erased parameter for runtime tree traversal,
# making them non-extractable to C via KaRaMeL. The Codec ImplTest
# IS fully verified with machine-checked proofs (see Codec.ImplTest.fst).
EXTRA_C_SOURCES   = fstar_support.c \
                    $(KRML_HOME)/krmllib/dist/generic/prims.c
CC_EXTRA_FLAGS    = -Wno-unused-but-set-variable
CC_EXTRA_INCLUDES = -I $(EXTRACT_DIR)/internal

include ../autoclrs.test.mk

# Ensure krmllib .krml files are built before KaRaMeL extraction
$(firstword $(EXTRACT_C_FILES)): $(KRMLLIB_KRML)
