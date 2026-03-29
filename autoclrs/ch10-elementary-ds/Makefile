PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
include $(PULSE_ROOT)/mk/test.mk
# Undo optimize_let_vc and fly_deps — they break modular arithmetic
# reasoning in Queue.fst dequeue proof
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --ext optimize_let_vc=false --ext fly_deps=false --include ../common

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

KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch10_*.krml \
                    $(KRML_HOME)/krmllib/.extract/FStar_Pervasives_Native.krml
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
EXTRA_LINK_LIBS   = $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a

include ../autoclrs.test.mk

# Override: extraction depends on the shell-loop step
$(firstword $(EXTRACT_C_FILES)): extract-krml

.PHONY: extract-krml
