PULSE_ROOT ?= ../../FStar/pulse
OTHERFLAGS += --include ../common
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID         = ch31

EXTRACT_MODULES = \
  CLRS.Ch31.GCD.ImplTest \
  CLRS.Ch31.GCD.Impl \
  CLRS.Ch31.GCD.Spec \
  CLRS.Ch31.GCD.Complexity \
  CLRS.Ch31.GCD.Lemmas \
  CLRS.Ch31.ModExp.ImplTest \
  CLRS.Ch31.ModExp.Impl \
  CLRS.Ch31.ModExp.Spec \
  CLRS.Ch31.ModExp.Complexity \
  CLRS.Ch31.ModExp.Lemmas \
  CLRS.Ch31.ModExpLR.ImplTest \
  CLRS.Ch31.ModExpLR.Impl \
  CLRS.Ch31.ModExpLR.Complexity \
  CLRS.Ch31.ModExpLR.Lemmas \
  CLRS.Common.Complexity

BUNDLE_C_STEM = CLRS_Ch31_GCD_ImplTest_CLRS_Ch31_ModExp_ImplTest_CLRS_Ch31_ModExpLR_ImplTest

KRML_INPUT_FILES  = $(foreach m,$(EXTRACT_MODULES),$(OUTPUT_DIR)/$(subst .,_,$m).krml)
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch31.GCD.ImplTest+CLRS.Ch31.ModExp.ImplTest+CLRS.Ch31.ModExpLR.ImplTest=CLRS.*' \
  -bundle 'FStar.*' -bundle 'Pulse.*' -bundle 'PulseCore.*' -bundle 'Prims'
KRML_WARN_FLAGS   = -warn-error -2-1-15
KRML_EXTRA_INPUTS = $(KRML_HOME)/krmllib/.extract/*.krml
EXTRACT_C_FILES   = $(OUTPUT_DIR)/$(BUNDLE_C_STEM).c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c
CC_EXTRA_FLAGS    = -Wno-implicit-function-declaration

include ../autoclrs.test.mk
