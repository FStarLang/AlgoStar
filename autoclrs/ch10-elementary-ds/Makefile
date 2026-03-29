PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
STAGE3     ?= 1
export STAGE3
include $(PULSE_ROOT)/mk/test.mk
OTHERFLAGS += --include ../common

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch10
EXTRACT_DIR       = $(OUTPUT_DIR)/csrc

EXTRACT_MODULES = \
  CLRS.Ch10.Stack.Impl \
  CLRS.Ch10.Stack.ImplTest \
  CLRS.Ch10.Queue.Impl \
  CLRS.Ch10.Queue.ImplTest \
  CLRS.Ch10.SinglyLinkedList.Base \
  CLRS.Ch10.SinglyLinkedList.Impl \
  CLRS.Ch10.SinglyLinkedList.ImplTest \
  CLRS.Ch10.DLL.Impl \
  CLRS.Ch10.DLL.ImplTest

# Step 1: extract each module to .krml (shell loop)
# Also extract FStar.Pervasives.Native (provides the option type for KaRaMeL)
extract-krml: __verify
	@echo "  [EXTRACT-KRML] Ch10 modules"
	@for mod in $(EXTRACT_MODULES); do \
	  krml_name=$$(echo "$$mod" | tr '.' '_'); \
	  if [ ! -f $(OUTPUT_DIR)/$$krml_name.krml ]; then \
	    checked=$(CACHE_DIR)/$$mod.fst.checked; \
	    if [ -f "$$checked" ]; then \
	      printf "    %-50s" "$$mod"; \
	      $(FSTAR) --codegen krml --extract_module "$$mod" "$$checked" > /dev/null 2>&1 && echo "OK" || echo "FAIL"; \
	    fi; \
	  fi; \
	done
	@if [ ! -f $(OUTPUT_DIR)/FStar_Pervasives_Native.krml ]; then \
	  printf "    %-50s" "FStar.Pervasives.Native"; \
	  $(FSTAR) --codegen krml --extract_module FStar.Pervasives.Native --odir $(OUTPUT_DIR) FStar.Pervasives.Native.fst > /dev/null 2>&1 && echo "OK" || echo "FAIL"; \
	fi

# KaRaMeL input files (must be listed explicitly — wildcards don't work as prerequisites)
KRML_INPUT_FILES  = $(patsubst %,$(OUTPUT_DIR)/%.krml, \
                      $(subst .,_,$(EXTRACT_MODULES)) FStar_Pervasives_Native)
KRML_BUNDLE_FLAGS = \
  -bundle "CLRS.Ch10.Stack.ImplTest=CLRS.Ch10.Stack.Impl,CLRS.Ch10.Stack.ImplTest" \
  -bundle "CLRS.Ch10.Queue.ImplTest=CLRS.Ch10.Queue.Impl,CLRS.Ch10.Queue.ImplTest" \
  -bundle "CLRS.Ch10.SinglyLinkedList.ImplTest=CLRS.Ch10.SinglyLinkedList.Base,CLRS.Ch10.SinglyLinkedList.Impl,CLRS.Ch10.SinglyLinkedList.ImplTest,FStar.Pervasives.Native" \
  -bundle "CLRS.Ch10.DLL.ImplTest=CLRS.Ch10.DLL.Impl,CLRS.Ch10.DLL.ImplTest"
KRML_WARN_FLAGS   = -warn-error -2-3-4-9-11-15-17
KRML_EXTRA_FLAGS  = -header $(PULSE_ROOT)/mk/krmlheader
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch10_Stack_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch10_Queue_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch10_SinglyLinkedList_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch10_DLL_ImplTest.c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c

include ../autoclrs.test.mk

# Override: all .krml and .c extraction comes from our shell-loop + KaRaMeL bundle,
# not the test.mk individual extraction pattern rules
$(KRML_INPUT_FILES): extract-krml ;
$(firstword $(EXTRACT_C_FILES)): extract-krml
$(EXTRACT_DIR)/%.c: extract-krml ;

.PHONY: extract-krml
