PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
OTHERFLAGS += --split_queries always
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch24
EXTRACT_DIR       = _output/c

KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch24_BellmanFord_ImplTest.krml \
                    $(OUTPUT_DIR)/CLRS_Ch24_BellmanFord_Impl.krml \
                    $(OUTPUT_DIR)/CLRS_Ch24_Dijkstra_ImplTest.krml \
                    $(OUTPUT_DIR)/CLRS_Ch24_Dijkstra_Impl.krml \
                    $(OUTPUT_DIR)/CLRS_Ch24_Dijkstra.krml \
                    $(OUTPUT_DIR)/CLRS_Ch24_ShortestPath_Inf.krml \
                    $(OUTPUT_DIR)/CLRS_Ch24_ShortestPath_Spec.krml
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch24.BellmanFord.ImplTest+CLRS.Ch24.Dijkstra.ImplTest=CLRS.Ch24.*[rename=Ch24_SSSP]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_WARN_FLAGS   = -warn-error -2-9-11-15-17
KRML_EXTRA_FLAGS  =
EXTRACT_C_FILES   = $(EXTRACT_DIR)/Ch24_SSSP.c
EXTRA_C_SOURCES   = fstar_support.c \
                    $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(EXTRACT_DIR)/krmlinit.c
CC_EXTRA_FLAGS    = -ffunction-sections -fdata-sections
EXTRA_LINK_LIBS   = -Wl,--gc-sections
TEST_EXE_NAME     = test_ch24

# Cancel Pulse's generic .krml → .c pattern rules for our extract dir
# (we use KaRaMeL batch extraction via autoclrs.test.mk instead)
$(EXTRACT_DIR)/%.krml:
	@true
$(EXTRACT_DIR)/%.c: $(EXTRACT_DIR)/%.krml
	@true

include ../autoclrs.test.mk
