PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
STAGE3     ?= 1
export STAGE3

include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID       = ch13
KRML_INPUT_FILES = $(OUTPUT_DIR)/CLRS_Ch13_RBTree_Main.krml \
                   $(OUTPUT_DIR)/CLRS_Ch13_RBTree_ImplTest.krml \
                   $(OUTPUT_DIR)/CLRS_Ch13_RBTree_Impl.krml \
                   $(OUTPUT_DIR)/CLRS_Ch13_RBTree_Spec.krml \
                   $(OUTPUT_DIR)/FStar_Pervasives_Native.krml \
                   $(OUTPUT_DIR)/FStar_Pervasives.krml
KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch13.RBTree.Main=CLRS.Ch13.RBTree.*' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_EXTRA_FLAGS  =
KRML_WARN_FLAGS   = -warn-error -2-15-20
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch13_RBTree_Main.c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(KRML_HOME)/krmllib/c/fstar_int32.c
TEST_MAIN         = test_main.c
TEST_EXE_NAME     = test_rbtree

include ../autoclrs.test.mk
