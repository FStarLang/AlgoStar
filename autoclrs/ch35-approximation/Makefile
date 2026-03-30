PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel

include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch35
EXTRACT_DIR       = $(OUTPUT_DIR)/c_extract
KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch35_VertexCover_ImplTest.krml \
                    $(OUTPUT_DIR)/CLRS_Ch35_VertexCover_Impl.krml
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch35.VertexCover.ImplTest+CLRS.Ch35.VertexCover.Impl=*[rename=VertexCoverTest]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,CLRS.Ch35.VertexCover.Spec,CLRS.Ch35.VertexCover.Lemmas,CLRS.Ch35.VertexCover.Complexity'
KRML_EXTRA_FLAGS  = -header=$(PULSE_ROOT)/mk/krmlheader
KRML_EXTRA_INPUTS = $(wildcard $(KRML_HOME)/krmllib/.extract/*.krml)
EXTRACT_C_FILES   = $(EXTRACT_DIR)/VertexCoverTest.c
TEST_EXE_NAME     = test_vertex_cover

include ../autoclrs.test.mk
