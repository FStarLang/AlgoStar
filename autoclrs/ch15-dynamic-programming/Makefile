KRML_HOME  ?= ../../FStar/karamel
KRML_EXE   ?= $(KRML_HOME)/krml
PULSE_ROOT ?= ../../FStar/pulse
include $(PULSE_ROOT)/mk/test.mk
OTHERFLAGS += --include ../common

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID  = ch15
EXTRACT_DIR = _extract

# Impl modules need full-dependency .krml because Pulse.Lib.BoundedIntegers
# .krml files are not available separately in krmllib.  The full-dep .krml
# bundles all transitive Pulse dependencies so KaRaMeL can generate C.
IMPL_MODULES = CLRS.Ch15.RodCutting.Impl \
               CLRS.Ch15.LCS.Impl \
               CLRS.Ch15.MatrixChain.Impl

# ImplTest per-module .krml (produced by test.mk pattern rule)
# Impl full-dependency .krml (produced by extract-impl-krml below)
KRML_INPUT_FILES = \
  $(OUTPUT_DIR)/CLRS_Ch15_RodCutting_ImplTest.krml \
  $(OUTPUT_DIR)/CLRS_Ch15_RodCutting_Impl_full.krml \
  $(OUTPUT_DIR)/CLRS_Ch15_LCS_ImplTest.krml \
  $(OUTPUT_DIR)/CLRS_Ch15_LCS_Impl_full.krml \
  $(OUTPUT_DIR)/CLRS_Ch15_MatrixChain_ImplTest.krml \
  $(OUTPUT_DIR)/CLRS_Ch15_MatrixChain_Impl_full.krml

# Full-dependency extraction for Impl modules
.PHONY: extract-impl-krml
extract-impl-krml: $(ALL_CHECKED_FILES)
	@for mod in $(IMPL_MODULES); do \
		krml=$$(echo $$mod | tr '.' '_')_full.krml; \
		if [ ! -f $(OUTPUT_DIR)/$$krml ]; then \
			echo "  Extracting $$mod (full deps)"; \
			rm -f $(OUTPUT_DIR)/out.krml; \
			$(FSTAR) --codegen krml $$mod.fst; \
			if [ -f $(OUTPUT_DIR)/out.krml ]; then \
				mv $(OUTPUT_DIR)/out.krml $(OUTPUT_DIR)/$$krml; \
			fi; \
		fi; \
	done

# Wire full-dep extraction as prerequisite of KaRaMeL step
$(OUTPUT_DIR)/CLRS_Ch15_RodCutting_Impl_full.krml \
$(OUTPUT_DIR)/CLRS_Ch15_LCS_Impl_full.krml \
$(OUTPUT_DIR)/CLRS_Ch15_MatrixChain_Impl_full.krml: extract-impl-krml
	@true

KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch15.RodCutting.ImplTest+CLRS.Ch15.RodCutting.Impl=CLRS.Ch15.RodCutting.ImplTest,CLRS.Ch15.RodCutting.Impl[rename=RodCutting_ImplTest]' \
  -bundle 'CLRS.Ch15.LCS.ImplTest+CLRS.Ch15.LCS.Impl=CLRS.Ch15.LCS.ImplTest,CLRS.Ch15.LCS.Impl[rename=LCS_ImplTest]' \
  -bundle 'CLRS.Ch15.MatrixChain.ImplTest+CLRS.Ch15.MatrixChain.Impl=CLRS.Ch15.MatrixChain.ImplTest,CLRS.Ch15.MatrixChain.Impl[rename=MatrixChain_ImplTest]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,CLRS.Ch15.RodCutting.Spec,CLRS.Ch15.RodCutting.Lemmas,CLRS.Ch15.LCS.Spec,CLRS.Ch15.LCS.Lemmas,CLRS.Ch15.MatrixChain.Spec,CLRS.Ch15.MatrixChain.Lemmas,CLRS.Ch15.MatrixChain.Complexity[rename=Support]'

# Warnings 11 (non-Low* expression) and 15 (non-Low* function) are expected:
# the Impl modules use nat/int via Pulse.Lib.BoundedIntegers for checked
# arithmetic, which KaRaMeL handles via krml_checked_int_t.
KRML_WARN_FLAGS = -warn-error -2-9-11-15-17

KRML_EXTRA_INPUTS = $(KRML_HOME)/krmllib/.extract/*.krml

# C files produced by KaRaMeL (all from one invocation)
EXTRACT_C_FILES = \
  $(EXTRACT_DIR)/RodCutting_ImplTest.c \
  $(EXTRACT_DIR)/LCS_ImplTest.c \
  $(EXTRACT_DIR)/MatrixChain_ImplTest.c \
  $(EXTRACT_DIR)/Support.c \
  $(EXTRACT_DIR)/krmlinit.c

EXTRA_C_SOURCES = \
  $(KRML_HOME)/krmllib/dist/generic/prims.c \
  $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c

CC_EXTRA_INCLUDES = -I $(EXTRACT_DIR)/internal

TEST_EXE_NAME = ch15_test

# Note: CLRS.Ch15.{RodCutting,MatrixChain}.Extended.fst are proof-only
# modules (verified Pulse code) not intended for C extraction. They extend
# the core algorithms but have no ImplTest or extraction targets.

# Cancel Pulse's generic .krml -> .c pattern rules for our extract dir
# (we use KaRaMeL batch extraction via autoclrs.test.mk instead)
$(EXTRACT_DIR)/%.krml:
	@true
$(EXTRACT_DIR)/%.c: $(EXTRACT_DIR)/%.krml
	@true

include ../autoclrs.test.mk
