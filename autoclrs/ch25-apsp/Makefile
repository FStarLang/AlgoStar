PULSE_ROOT ?= ../../pulse

# KaRaMeL for C extraction
KRML_HOME ?= ../../krml/karamel
KRML_EXE  ?= $(KRML_HOME)/krml

include $(PULSE_ROOT)/mk/test.mk

# ============================================================================
# C Extraction via KaRaMeL
# ============================================================================

EXTRACT_DIR = _extract

# Modules to extract (only implementation modules; specs/lemmas are erased)
CH25_MODULES = \
  CLRS.Ch25.FloydWarshall.Impl \
  CLRS.Ch25.FloydWarshall.NegCycleDetect

$(EXTRACT_DIR):
	mkdir -p $@ $@/internal

# Step 1: Extract each module to .krml
extract-krml: __verify | $(EXTRACT_DIR)
	@echo "=== Extracting ch25 modules to .krml ==="
	@for mod in $(CH25_MODULES); do \
		fst_file=$$mod.fst; \
		if [ -f "$$fst_file" ]; then \
			echo "  Extracting $$mod"; \
			$(FSTAR) --codegen krml --extract_module $$mod $$fst_file; \
		fi; \
	done
	@echo ".krml files written to $(OUTPUT_DIR)/"

# Step 2: .krml → C via KaRaMeL
#   Bundle Impl + NegCycleDetect into a single C file.
#   ImplTest is not included because Pulse test functions are ghost-erased;
#   the C test driver (test_main.c) exercises the API directly.
extract-c: extract-krml | $(EXTRACT_DIR)
	@echo "=== Running KaRaMeL ==="
	$(KRML_EXE) \
		-tmpdir $(EXTRACT_DIR) \
		-skip-compilation \
		-warn-error -2-9-11-15-17 \
		-bundle 'CLRS.Ch25.FloydWarshall.NegCycleDetect+CLRS.Ch25.FloydWarshall.Impl=CLRS.*,Prims,FStar.*,Pulse.*,PulseCore.*[rename=CLRS_Ch25_FloydWarshall]' \
		-no-prefix CLRS.Ch25.FloydWarshall.Impl \
		-no-prefix CLRS.Ch25.FloydWarshall.NegCycleDetect \
		$(wildcard $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_Impl.krml) \
		$(wildcard $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_NegCycleDetect.krml) \
		$(KRML_HOME)/krmllib/.extract/*.krml
	@echo "C files written to $(EXTRACT_DIR)/"
	@ls $(EXTRACT_DIR)/*.c $(EXTRACT_DIR)/*.h 2>/dev/null || true

# Step 3: Compile and run extracted C test
test-c: extract-c
	@echo "=== Compiling extracted C ==="
	gcc -std=c11 -Wall -Wno-unused-variable -Wno-parentheses \
		-g \
		-I$(EXTRACT_DIR) \
		-I$(KRML_HOME)/include \
		-I$(KRML_HOME)/krmllib/dist/minimal \
		-o $(EXTRACT_DIR)/test_ch25 \
		$(EXTRACT_DIR)/CLRS_Ch25_FloydWarshall.c \
		test_main.c
	@echo "=== Running extracted test ==="
	$(EXTRACT_DIR)/test_ch25
	@echo "=== Running extracted test ==="
	$(EXTRACT_DIR)/test_ch25

.PHONY: extract-krml extract-c test-c
