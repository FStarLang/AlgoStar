PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk
# Undo optimize_let_vc and fly_deps — they break SizeT overflow
# reasoning in MatrixChain.fst
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --ext optimize_let_vc=false --ext fly_deps=false --include ../common

# ============================================================================
# C extraction and test targets
# ============================================================================

KRML_HOME ?= ../../krml/karamel
KRML_EXE  ?= $(KRML_HOME)/krml
KRMLLIB   ?= $(KRML_HOME)/krmllib/.extract
EXTRACT_DIR = _extract

IMPLTEST_MODULES = CLRS.Ch15.RodCutting.ImplTest \
                   CLRS.Ch15.LCS.ImplTest \
                   CLRS.Ch15.MatrixChain.ImplTest

$(EXTRACT_DIR):
	mkdir -p $@

# Step 1: Extract each ImplTest module to .krml (includes Pulse deps via out.krml)
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

# Step 2: KaRaMeL translates .krml to C headers
extract-c: extract-krml | $(EXTRACT_DIR)
	@echo "=== Running KaRaMeL ==="
	$(KRML_EXE) \
		-tmpdir $(EXTRACT_DIR) \
		-skip-compilation \
		-warn-error -2-9-11-15-17 \
		-add-include '"krml/internal/compat.h"' \
		-bundle 'FStar.*,Prims' \
		$(OUTPUT_DIR)/CLRS_Ch15_RodCutting_ImplTest.krml \
		$(OUTPUT_DIR)/CLRS_Ch15_LCS_ImplTest.krml \
		$(OUTPUT_DIR)/CLRS_Ch15_MatrixChain_ImplTest.krml \
		$(KRMLLIB)/*.krml
	@echo "C headers written to $(EXTRACT_DIR)/"

# Step 3: Compile and run the C test driver
#   The test_main.c contains hand-written C implementations that mirror
#   the verified Pulse algorithms exactly. Since the Pulse while-loop
#   pattern uses closures that KaRaMeL cannot translate to C directly,
#   the C implementations are written manually to match the verified code.
test-c: | $(EXTRACT_DIR)
	@echo "=== Compiling C test driver ==="
	$(CC) -O2 -Wall -Wextra -o $(EXTRACT_DIR)/test_main test_main.c
	@echo "=== Running C tests ==="
	@$(EXTRACT_DIR)/test_main

.PHONY: extract-krml extract-c test-c
