PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel

include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID  = ch25
EXTRACT_DIR = _extract

CH25_MODULES = \
  CLRS.Ch25.FloydWarshall.Impl \
  CLRS.Ch25.FloydWarshall.NegCycleDetect

# Step 1: Extract each module to .krml (shell loop, depends on __verify)
extract-krml: __verify
	@echo "=== Extracting ch25 modules to .krml ==="
	@mkdir -p $(EXTRACT_DIR) $(EXTRACT_DIR)/internal
	@for mod in $(CH25_MODULES); do \
		fst_file=$$mod.fst; \
		if [ -f "$$fst_file" ]; then \
			echo "  Extracting $$mod"; \
			$(FSTAR) --codegen krml --extract_module $$mod $$fst_file; \
		fi; \
	done

KRML_INPUT_FILES  = $(wildcard $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_Impl.krml) \
                    $(wildcard $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_NegCycleDetect.krml)
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch25.FloydWarshall.NegCycleDetect+CLRS.Ch25.FloydWarshall.Impl=CLRS.*,Prims,FStar.*,Pulse.*,PulseCore.*[rename=CLRS_Ch25_FloydWarshall]' 
KRML_EXTRA_FLAGS  = \
  -no-prefix CLRS.Ch25.FloydWarshall.Impl \
  -no-prefix CLRS.Ch25.FloydWarshall.NegCycleDetect
KRML_EXTRA_INPUTS =
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch25_FloydWarshall.c
TEST_MAIN         = test_main.c
TEST_EXE_NAME     = test_ch25

include ../autoclrs.test.mk

# Override: extraction depends on the shell-loop step
$(firstword $(EXTRACT_C_FILES)): extract-krml
