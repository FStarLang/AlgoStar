PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
include $(PULSE_ROOT)/mk/test.mk
OTHERFLAGS += --include ../common

# ââ C extraction and test targets ââââââââââââââââââââââââââââââââââââââââââââ
CHAPTER_ID  = ch32
EXTRACT_DIR = _extract

# Only Impl + ImplTest modules are extracted to C.
# Spec/Lemma/Complexity/Bridge modules are proof-only (not extracted).
EXTRACT_MODULES = \
  CLRS.Ch32.NaiveStringMatch.ImplTest \
  CLRS.Ch32.NaiveStringMatch \
  CLRS.Ch32.KMP.ImplTest \
  CLRS.Ch32.KMP \
  CLRS.Ch32.RabinKarp.ImplTest \
  CLRS.Ch32.RabinKarp

KRML_INPUT_FILES = $(foreach m,$(EXTRACT_MODULES),$(OUTPUT_DIR)/$(subst .,_,$(m)).krml)

KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch32.NaiveStringMatch.ImplTest+CLRS.Ch32.KMP.ImplTest+CLRS.Ch32.RabinKarp.ImplTest+CLRS.Ch32.NaiveStringMatch+CLRS.Ch32.KMP+CLRS.Ch32.RabinKarp=[rename=Ch32_StringMatch]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_EXTRA_FLAGS  = \
  -no-prefix 'CLRS.Ch32.NaiveStringMatch.ImplTest' \
  -no-prefix 'CLRS.Ch32.KMP.ImplTest' \
  -no-prefix 'CLRS.Ch32.RabinKarp.ImplTest' \
  -no-prefix 'CLRS.Ch32.NaiveStringMatch' \
  -no-prefix 'CLRS.Ch32.KMP' \
  -no-prefix 'CLRS.Ch32.RabinKarp'
KRML_EXTRA_INPUTS = $(KRML_HOME)/krmllib/.extract/*.krml
EXTRACT_C_FILES   = $(EXTRACT_DIR)/Ch32_StringMatch.c
# prims.c provides Prims_op_* (checked int arithmetic used by RabinKarp's int/nat computations)
# fstar_int32.c provides FStar_Int32_to_string (dependency of prims.c)
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c
CC_EXTRA_FLAGS    = -Wno-unused-function
CC_EXTRA_INCLUDES = -I $(EXTRACT_DIR)/internal

# Cancel Pulse's generic pattern rules for the extract dir
$(EXTRACT_DIR)/%.krml:
	@true
$(EXTRACT_DIR)/%.c: $(EXTRACT_DIR)/%.krml
	@true

include ../autoclrs.test.mk

clean: __clean_extract
.PHONY: __clean_extract
__clean_extract:
	rm -rf $(EXTRACT_DIR)
