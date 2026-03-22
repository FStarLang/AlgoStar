PULSE_ROOT ?= ../../pulse
KRML_HOME  ?= ../../krml/karamel
include $(PULSE_ROOT)/mk/test.mk
# Undo optimize_let_vc and fly_deps — they break modular arithmetic
# reasoning in Queue.fst dequeue proof
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --ext optimize_let_vc=false --ext fly_deps=false --include ../common

# ---------- C extraction and testing ----------

KRML_EXE  ?= $(KRML_HOME)/krml
CSRC_DIR   = $(OUTPUT_DIR)/csrc

# Modules to extract (ImplTest + Impl deps)
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

# Step 1: extract each module to .krml
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

# Step 2: convert .krml → .c/.h via krml
extract-c: extract-krml
	@echo "  [KRML] Ch10 → C"
	@mkdir -p $(CSRC_DIR)
	$(KRML_EXE) \
	  -skip-makefiles -skip-linking \
	  -warn-error -2-3-4-9-11-15-17 \
	  -header $(PULSE_ROOT)/mk/krmlheader \
	  -bundle "CLRS.Ch10.Stack.ImplTest=CLRS.Ch10.Stack.Impl,CLRS.Ch10.Stack.ImplTest" \
	  -bundle "CLRS.Ch10.Queue.ImplTest=CLRS.Ch10.Queue.Impl,CLRS.Ch10.Queue.ImplTest" \
	  -bundle "CLRS.Ch10.SinglyLinkedList.ImplTest=CLRS.Ch10.SinglyLinkedList.Base,CLRS.Ch10.SinglyLinkedList.Impl,CLRS.Ch10.SinglyLinkedList.ImplTest,FStar.Pervasives.Native" \
	  -bundle "CLRS.Ch10.DLL.ImplTest=CLRS.Ch10.DLL.Impl,CLRS.Ch10.DLL.ImplTest" \
	  $(OUTPUT_DIR)/CLRS_Ch10_*.krml \
	  $(KRML_HOME)/krmllib/.extract/FStar_Pervasives_Native.krml \
	  -tmpdir $(CSRC_DIR)

# Step 3: compile C to executable
build-test: extract-c
	@echo "  [CC] ch10_test"
	cc -std=c11 -g -fwrapv -D_BSD_SOURCE -D_DEFAULT_SOURCE \
	  -I $(CSRC_DIR) \
	  -I $(KRML_HOME)/krmllib/dist/minimal \
	  -I $(KRML_HOME)/krmllib \
	  -I $(KRML_HOME)/include \
	  -Wall -Wno-parentheses -Wno-unused-variable \
	  -o $(CSRC_DIR)/ch10_test \
	  main.c \
	  $(CSRC_DIR)/CLRS_Ch10_Stack_ImplTest.c \
	  $(CSRC_DIR)/CLRS_Ch10_Queue_ImplTest.c \
	  $(CSRC_DIR)/CLRS_Ch10_SinglyLinkedList_ImplTest.c \
	  $(CSRC_DIR)/CLRS_Ch10_DLL_ImplTest.c \
	  $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a

# Step 4: run the test
test-c: build-test
	@echo "  [RUN] ch10_test"
	@$(CSRC_DIR)/ch10_test

.PHONY: extract-krml extract-c build-test test-c
