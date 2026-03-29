PULSE_ROOT ?= ../../FStar/pulse
include $(PULSE_ROOT)/mk/test.mk
OTHERFLAGS += --include ../common

# ── C extraction targets ──────────────────────────────────────────
CHAPTER_ID  = ch15
EXTRACT_DIR = _extract

IMPLTEST_MODULES = CLRS.Ch15.RodCutting.ImplTest \
                   CLRS.Ch15.LCS.ImplTest \
                   CLRS.Ch15.MatrixChain.ImplTest

# Step 1: Extract each ImplTest module to .krml (shell loop)
extract-krml: $(ALL_CHECKED_FILES)
	@echo "=== Extracting ImplTest modules to .krml ==="
	@for mod in $(IMPLTEST_MODULES); do \
		echo "  Extracting $$mod"; \
		rm -f $(OUTPUT_DIR)/out.krml; \
		$(FSTAR) --codegen krml \
			$$(echo $$mod | tr '.' '/').fst; \
		krml=$$(echo $$mod | tr '.' '_').krml; \
		if [ -f $(OUTPUT_DIR)/out.krml ]; then \
			mv $(OUTPUT_DIR)/out.krml $(OUTPUT_DIR)/$$krml; \
			echo "    -> $$krml ($$(stat -c%s $(OUTPUT_DIR)/$$krml) bytes)"; \
		else \
			echo "    -> $$krml ($(OUTPUT_DIR)/$$krml, $$(stat -c%s $(OUTPUT_DIR)/$$krml 2>/dev/null || echo 0) bytes)"; \
		fi; \
	done

KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch15_RodCutting_ImplTest.krml \
                    $(OUTPUT_DIR)/CLRS_Ch15_LCS_ImplTest.krml \
                    $(OUTPUT_DIR)/CLRS_Ch15_MatrixChain_ImplTest.krml
KRML_BUNDLE_FLAGS = -bundle 'FStar.*,Prims'
KRML_EXTRA_INPUTS = $(KRML_HOME)/krmllib/.extract/*.krml
# KaRaMeL produces headers; the actual C test is hand-written
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch15_RodCutting_ImplTest.c

# Override: extraction depends on the shell-loop step
$(firstword $(EXTRACT_C_FILES)): extract-krml
	@mkdir -p $(EXTRACT_DIR)
	$(KRML_EXE) \
		-tmpdir $(EXTRACT_DIR) \
		-skip-compilation \
		$(KRML_WARN_FLAGS) \
		-add-include '"krml/internal/compat.h"' \
		$(KRML_BUNDLE_FLAGS) \
		$(KRML_INPUT_FILES) \
		$(KRML_EXTRA_INPUTS)

# The C test driver is self-contained (mirrors the verified algorithms)
TEST_MAIN         = test_main.c
EXTRA_C_SOURCES   =
CC_EXTRA_FLAGS    = -O2 -Wextra

$(EXTRACT_DIR)/$(CHAPTER_ID)_test: $(TEST_MAIN)
	@mkdir -p $(EXTRACT_DIR)
	$(call msg, "CC", "$(CHAPTER_ID)_test")
	$(CC) -O2 -Wall -Wextra -o $@ $(TEST_MAIN)

$(EXTRACT_DIR)/$(CHAPTER_ID)_test.out: $(EXTRACT_DIR)/$(CHAPTER_ID)_test
	$(call msg, "RUN", "$(CHAPTER_ID)_test")
	./$< | tee $@

.PHONY: extract-krml extract test-c
extract: $(EXTRACT_C_FILES)
test-c: $(EXTRACT_DIR)/$(CHAPTER_ID)_test.out
