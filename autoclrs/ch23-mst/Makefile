PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk
# Undo optimize_let_vc and fly_deps — they break SizeT overflow
# reasoning in Prim.fst
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --ext optimize_let_vc=false --ext fly_deps=false --include ../common

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch23
EXTRACT_DIR       = _output/c

KRML_INPUT_FILES  = _output/CLRS_Ch23_Prim_ImplTest.krml \
                    _output/CLRS_Ch23_Prim_Impl.krml \
                    _output/CLRS_Ch23_Kruskal_ImplTest.krml \
                    _output/CLRS_Ch23_Kruskal_Impl.krml \
                    _output/CLRS_Ch23_MST_Spec.krml \
                    _output/CLRS_Ch23_Kruskal_Defs.krml \
                    _output/CLRS_Ch23_Kruskal_EdgeSorting.krml
KRML_BUNDLE_FLAGS = -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_WARN_FLAGS   = -warn-error -2-9-11-15-17
KRML_EXTRA_FLAGS  =
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch23_Prim_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch23_Prim_Impl.c \
                    $(EXTRACT_DIR)/CLRS_Ch23_Kruskal_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch23_Kruskal_Impl.c
EXTRA_C_SOURCES   = fstar_support.c \
                    $(KRML_HOME)/krmllib/dist/generic/prims.c
TEST_EXE_NAME     = mst_test.exe

# Cancel Pulse's generic .krml → .c pattern rules for our extract dir
# (we use KaRaMeL batch extraction via autoclrs.test.mk instead)
$(EXTRACT_DIR)/%.krml:
	@true
$(EXTRACT_DIR)/%.c: $(EXTRACT_DIR)/%.krml
	@true

include ../autoclrs.test.mk
