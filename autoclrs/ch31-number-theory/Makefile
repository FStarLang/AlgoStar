PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
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
  CLRS.Ch31.ExtendedGCD.ImplTest \
  CLRS.Ch31.ExtendedGCD.Impl \
  CLRS.Ch31.ExtendedGCD.Spec \
  CLRS.Ch31.ExtendedGCD.Complexity \
  CLRS.Ch31.ExtendedGCD.Lemmas \
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

BUNDLE_C_STEM = Ch31_NumberTheory

KRML_INPUT_FILES  = $(foreach m,$(EXTRACT_MODULES),$(OUTPUT_DIR)/$(subst .,_,$m).krml)
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch31.GCD.ImplTest+CLRS.Ch31.ExtendedGCD.ImplTest+CLRS.Ch31.ModExp.ImplTest+CLRS.Ch31.ModExpLR.ImplTest=CLRS.*[rename=Ch31_NumberTheory]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_WARN_FLAGS   = -warn-error -2-9-15-17
KRML_EXTRA_INPUTS =
EXTRACT_C_FILES   = $(OUTPUT_DIR)/$(BUNDLE_C_STEM).c
EXTRA_C_SOURCES   =
CC_EXTRA_FLAGS    =

include ../autoclrs.test.mk
