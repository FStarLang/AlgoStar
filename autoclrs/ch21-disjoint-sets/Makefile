PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk
# Add explicit include for common directory (fly_deps doesn't resolve it)
OTHERFLAGS += --include ../common

# ========== C extraction and test targets ==========
KRML_HOME ?= ../../krml/karamel
KRML      := $(KRML_HOME)/krml

# Modules to extract to krml
KRML_FILES = $(OUTPUT_DIR)/CLRS_Ch21_UnionFind_ImplTest.krml \
             $(OUTPUT_DIR)/CLRS_Ch21_UnionFind_Impl.krml

# Extract F* modules to .krml
$(OUTPUT_DIR)/CLRS_Ch21_UnionFind_ImplTest.krml: _cache/CLRS.Ch21.UnionFind.ImplTest.fst.checked
	$(call msg, "EXTRACT", "CLRS.Ch21.UnionFind.ImplTest")
	$(FSTAR) $< --codegen krml --extract_module CLRS.Ch21.UnionFind.ImplTest

$(OUTPUT_DIR)/CLRS_Ch21_UnionFind_Impl.krml: _cache/CLRS.Ch21.UnionFind.Impl.fst.checked
	$(call msg, "EXTRACT", "CLRS.Ch21.UnionFind.Impl")
	$(FSTAR) $< --codegen krml --extract_module CLRS.Ch21.UnionFind.Impl

# Run krml to generate C from .krml files
$(OUTPUT_DIR)/CLRS_Ch21_UnionFind_ImplTest.c: $(KRML_FILES)
	$(call msg, "KRML", "CLRS_Ch21_UnionFind_ImplTest")
	$(KRML) -skip-compilation -skip-makefiles \
	  -bundle 'CLRS.Ch21.UnionFind.ImplTest=CLRS.Ch21.UnionFind.*' \
	  -bundle 'FStar.*' -bundle 'Prims' -bundle 'C' \
	  -warn-error '-2-4-11-15' \
	  -tmpdir $(OUTPUT_DIR) \
	  $(KRML_HOME)/krmllib/.extract/*.krml \
	  $^

# Compile C to executable
$(OUTPUT_DIR)/test_union_find: $(OUTPUT_DIR)/CLRS_Ch21_UnionFind_ImplTest.c main.c
	$(call msg, "CC", "test_union_find")
	$(CC) -Wall -Wno-unused-variable \
	  -I $(KRML_HOME)/include \
	  -I $(KRML_HOME)/krmllib/dist/generic \
	  -I $(OUTPUT_DIR) \
	  -o $@ \
	  $(OUTPUT_DIR)/CLRS_Ch21_UnionFind_ImplTest.c \
	  main.c \
	  $(KRML_HOME)/krmllib/dist/generic/c.c

# Run the test
$(OUTPUT_DIR)/test_union_find.out: $(OUTPUT_DIR)/test_union_find
	$(call msg, "RUN", "test_union_find")
	./$< > $@ 2>&1
	@cat $@

.PHONY: extract test-c
extract: $(OUTPUT_DIR)/CLRS_Ch21_UnionFind_ImplTest.c
test-c: $(OUTPUT_DIR)/test_union_find.out
