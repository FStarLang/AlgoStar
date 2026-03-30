PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel

include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch25
EXTRACT_DIR       = _extract

KRML_INPUT_FILES  = $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_Impl.krml \
                    $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_NegCycleDetect.krml \
                    $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_ImplTest.krml \
                    $(OUTPUT_DIR)/CLRS_Ch25_FloydWarshall_Spec.krml

KRML_BUNDLE_FLAGS = \
  -bundle 'CLRS.Ch25.FloydWarshall.ImplTest+CLRS.Ch25.FloydWarshall.NegCycleDetect+CLRS.Ch25.FloydWarshall.Impl=CLRS.*,Prims,FStar.*,Pulse.*,PulseCore.*[rename=CLRS_Ch25_FloydWarshall]'

KRML_EXTRA_FLAGS  = \
  -no-prefix CLRS.Ch25.FloydWarshall.Impl \
  -no-prefix CLRS.Ch25.FloydWarshall.NegCycleDetect \
  -no-prefix CLRS.Ch25.FloydWarshall.ImplTest

EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch25_FloydWarshall.c
TEST_MAIN         = test_main.c
TEST_EXE_NAME     = test_ch25

EXTRA_C_SOURCES   = fstar_support.c \
                    $(KRML_HOME)/krmllib/dist/generic/prims.c

include ../autoclrs.test.mk
