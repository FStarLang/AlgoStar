PULSE_ROOT ?= ../../pulse
KRML_HOME  ?= ../../krml/karamel

include $(PULSE_ROOT)/mk/test.mk

# ---------------------------------------------------------------------------
# C extraction and test targets for ImplTest
# ---------------------------------------------------------------------------
EXTRACT_DIR = $(OUTPUT_DIR)/c_extract

KRML_FILES = $(OUTPUT_DIR)/CLRS_Ch35_VertexCover_ImplTest.krml \
             $(OUTPUT_DIR)/CLRS_Ch35_VertexCover_Impl.krml

# Step 1: Extract F* modules to .krml (rules inherited from test.mk)

# Step 2: Run KaRaMeL to produce C
$(EXTRACT_DIR)/VertexCoverTest.c: $(KRML_FILES)
	@mkdir -p $(EXTRACT_DIR)/internal
	$(KRML_HOME)/krml \
	  -skip-makefiles \
	  -skip-linking \
	  -skip-compilation \
	  -header=$(PULSE_ROOT)/mk/krmlheader \
	  -add-include '"krml/internal/compat.h"' \
	  -warn-error -2-9-11-15-17 \
	  -bundle 'CLRS.Ch35.VertexCover.ImplTest+CLRS.Ch35.VertexCover.Impl=*[rename=VertexCoverTest]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -tmpdir $(EXTRACT_DIR) \
	  $(KRML_FILES) \
	  $(KRML_HOME)/krmllib/.extract/*.krml

# Step 3: Compile C to executable
$(EXTRACT_DIR)/test_vertex_cover: $(EXTRACT_DIR)/VertexCoverTest.c main.c
	cc -o $@ \
	  -I $(KRML_HOME)/krmllib/dist/minimal \
	  -I $(KRML_HOME)/krmllib \
	  -I $(KRML_HOME)/include \
	  -I $(EXTRACT_DIR) \
	  -Wall -Wno-parentheses -g -std=c11 \
	  main.c $(EXTRACT_DIR)/VertexCoverTest.c

# Step 4: Run the test
$(EXTRACT_DIR)/test_vertex_cover.out: $(EXTRACT_DIR)/test_vertex_cover
	./$< | tee $@

.PHONY: extract-c test-c
extract-c: $(EXTRACT_DIR)/VertexCoverTest.c
test-c: $(EXTRACT_DIR)/test_vertex_cover.out
