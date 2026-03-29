KRML_HOME  ?= ../../FStar/karamel
KRML_EXE   ?= $(KRML_HOME)/krml
PULSE_ROOT ?= ../../FStar/pulse
include $(PULSE_ROOT)/mk/test.mk
OTHERFLAGS += --include ../common

# ── C extraction targets ──────────────────────────────────────────
CHAPTER_ID  = ch15
EXTRACT_DIR = _extract

# Modules to extract: each ImplTest + its Impl
IMPLTEST_MODULES = CLRS.Ch15.RodCutting.ImplTest \
                   CLRS.Ch15.LCS.ImplTest \
                   CLRS.Ch15.MatrixChain.ImplTest

IMPL_MODULES     = CLRS.Ch15.RodCutting.Impl \
                   CLRS.Ch15.LCS.Impl \
                   CLRS.Ch15.MatrixChain.Impl

# Step 1a: Extract each ImplTest to a per-module .krml (from .checked)
# These small .krml files contain only the test module's AST.
IMPLTEST_KRMLS = $(patsubst %,$(OUTPUT_DIR)/$(subst .,_,%).krml,$(IMPLTEST_MODULES))

# Step 1b: Extract each Impl to a full-dependency .krml (from .fst)
# These larger .krml files include all transitive dependencies (Pulse
# primitives, etc.) so KaRaMeL can compile Pulse fn bodies to C.
IMPL_KRMLS = $(patsubst %,$(OUTPUT_DIR)/%_full.krml,$(subst .,_,$(IMPL_MODULES)))

# The per-module extraction uses test.mk's pattern rule automatically.
# The full-dependency extraction needs a custom rule:
extract-impl-krml: $(ALL_CHECKED_FILES)
	@for mod in $(IMPL_MODULES); do \
		echo "  Extracting $$mod (full deps)"; \
		rm -f $(OUTPUT_DIR)/out.krml; \
		$(FSTAR) --codegen krml $$mod.fst; \
		krml=$$(echo $$mod | tr '.' '_')_full.krml; \
		if [ -f $(OUTPUT_DIR)/out.krml ]; then \
			mv $(OUTPUT_DIR)/out.krml $(OUTPUT_DIR)/$$krml; \
		fi; \
	done

extract-impltest-krml: $(ALL_CHECKED_FILES)
	@for mod in $(IMPLTEST_MODULES); do \
		checked=$$(echo $$mod | tr '/' '.').fst.checked; \
		echo "  Extracting $$mod (per-module)"; \
		$(FSTAR) --codegen krml --extract_module $$mod $(CACHE_DIR)/$$checked; \
	done

# Step 2: KaRaMeL .krml → .c
KRML_WARN_FLAGS   ?= -warn-error -2-9-11-15-17

KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch15.RodCutting.ImplTest+CLRS.Ch15.RodCutting.Impl=CLRS.Ch15.RodCutting.ImplTest,CLRS.Ch15.RodCutting.Impl[rename=RodCutting_ImplTest]' \
  -bundle 'CLRS.Ch15.LCS.ImplTest+CLRS.Ch15.LCS.Impl=CLRS.Ch15.LCS.ImplTest,CLRS.Ch15.LCS.Impl[rename=LCS_ImplTest]' \
  -bundle 'CLRS.Ch15.MatrixChain.ImplTest+CLRS.Ch15.MatrixChain.Impl=CLRS.Ch15.MatrixChain.ImplTest,CLRS.Ch15.MatrixChain.Impl[rename=MatrixChain_ImplTest]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,CLRS.Ch15.RodCutting.Spec,CLRS.Ch15.RodCutting.Lemmas,CLRS.Ch15.LCS.Spec,CLRS.Ch15.LCS.Lemmas,CLRS.Ch15.MatrixChain.Spec,CLRS.Ch15.MatrixChain.Lemmas,CLRS.Ch15.MatrixChain.Complexity[rename=Support]'

KRML_EXTRA_INPUTS = $(KRML_HOME)/krmllib/.extract/*.krml

EXTRACT_C_FILES   = $(EXTRACT_DIR)/RodCutting_ImplTest.c \
                    $(EXTRACT_DIR)/LCS_ImplTest.c \
                    $(EXTRACT_DIR)/MatrixChain_ImplTest.c

$(firstword $(EXTRACT_C_FILES)): extract-impl-krml extract-impltest-krml
	@mkdir -p $(EXTRACT_DIR)
	$(KRML_EXE) \
		-skip-makefiles -skip-compilation -skip-linking \
		$(KRML_WARN_FLAGS) \
		-add-include '"krml/internal/compat.h"' \
		$(KRML_BUNDLE_FLAGS) \
		-tmpdir $(EXTRACT_DIR) \
		$(OUTPUT_DIR)/CLRS_Ch15_RodCutting_ImplTest.krml \
		$(OUTPUT_DIR)/CLRS_Ch15_RodCutting_Impl_full.krml \
		$(OUTPUT_DIR)/CLRS_Ch15_LCS_ImplTest.krml \
		$(OUTPUT_DIR)/CLRS_Ch15_LCS_Impl_full.krml \
		$(OUTPUT_DIR)/CLRS_Ch15_MatrixChain_ImplTest.krml \
		$(OUTPUT_DIR)/CLRS_Ch15_MatrixChain_Impl_full.krml \
		$(KRML_EXTRA_INPUTS)

# All .c files are produced by the single krml invocation above
$(wordlist 2,$(words $(EXTRACT_C_FILES)),$(EXTRACT_C_FILES)): $(firstword $(EXTRACT_C_FILES))
	@:

# Step 3: Compile and link
KRML_CC_INCLUDES = \
  -I $(KRML_HOME)/include \
  -I $(KRML_HOME)/krmllib/dist/minimal \
  -I $(KRML_HOME)/krmllib/dist/generic \
  -I $(KRML_HOME)/krmllib \
  -I $(EXTRACT_DIR) \
  -I $(EXTRACT_DIR)/internal \
  -I .

KRML_CC_FLAGS = -std=c11 -Wall -g -fwrapv \
  -D_BSD_SOURCE -D_DEFAULT_SOURCE \
  -Wno-unused-variable -Wno-unused-parameter -Wno-parentheses

EXTRA_C_SOURCES = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                  $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c

$(EXTRACT_DIR)/$(CHAPTER_ID)_test: $(EXTRACT_C_FILES) main.c
	@mkdir -p $(EXTRACT_DIR)
	$(call msg, "CC+LINK", "$(CHAPTER_ID)_test")
	$(CC) $(KRML_CC_FLAGS) $(KRML_CC_INCLUDES) \
		-o $@ main.c \
		$(EXTRACT_C_FILES) $(EXTRACT_DIR)/Support.c \
		$(EXTRA_C_SOURCES)

$(EXTRACT_DIR)/$(CHAPTER_ID)_test.out: $(EXTRACT_DIR)/$(CHAPTER_ID)_test
	$(call msg, "RUN", "$(CHAPTER_ID)_test")
	./$< | tee $@

.PHONY: extract-impl-krml extract-impltest-krml extract test-c
extract: $(EXTRACT_C_FILES)
test-c: $(EXTRACT_DIR)/$(CHAPTER_ID)_test.out
