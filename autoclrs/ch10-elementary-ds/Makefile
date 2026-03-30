PULSE_ROOT ?= ../../FStar/pulse
KRML_HOME  ?= ../../FStar/karamel
include $(PULSE_ROOT)/mk/test.mk
OTHERFLAGS += --include ../common

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch10
EXTRACT_DIR       = _output/c

KRML_INPUT_FILES  = _output/CLRS_Ch10_Stack_Impl.krml \
                    _output/CLRS_Ch10_Stack_ImplTest.krml \
                    _output/CLRS_Ch10_Queue_Impl.krml \
                    _output/CLRS_Ch10_Queue_ImplTest.krml \
                    _output/CLRS_Ch10_SinglyLinkedList_Base.krml \
                    _output/CLRS_Ch10_SinglyLinkedList_Impl.krml \
                    _output/CLRS_Ch10_SinglyLinkedList_ImplTest.krml \
                    _output/CLRS_Ch10_DLL_Impl.krml \
                    _output/CLRS_Ch10_DLL_ImplTest.krml \
                    _output/FStar_Pervasives_Native.krml
KRML_BUNDLE_FLAGS = \
  -bundle "CLRS.Ch10.Stack.ImplTest=CLRS.Ch10.Stack.Impl,CLRS.Ch10.Stack.ImplTest" \
  -bundle "CLRS.Ch10.Queue.ImplTest=CLRS.Ch10.Queue.Impl,CLRS.Ch10.Queue.ImplTest" \
  -bundle "CLRS.Ch10.SinglyLinkedList.ImplTest=CLRS.Ch10.SinglyLinkedList.Base,CLRS.Ch10.SinglyLinkedList.Impl,CLRS.Ch10.SinglyLinkedList.ImplTest,FStar.Pervasives.Native" \
  -bundle "CLRS.Ch10.DLL.ImplTest=CLRS.Ch10.DLL.Impl,CLRS.Ch10.DLL.ImplTest" \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_WARN_FLAGS   = -warn-error -2-9-11-15-17
KRML_EXTRA_FLAGS  = -header $(PULSE_ROOT)/mk/krmlheader
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch10_Stack_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch10_Queue_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch10_SinglyLinkedList_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch10_DLL_ImplTest.c
EXTRA_C_SOURCES   = $(KRML_HOME)/krmllib/dist/generic/prims.c \
                    $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c

# Cancel Pulse's generic .krml → .c pattern rules for our extract dir
# (we use KaRaMeL batch extraction via autoclrs.test.mk instead)
$(EXTRACT_DIR)/%.krml:
	@true
$(EXTRACT_DIR)/%.c: $(EXTRACT_DIR)/%.krml
	@true

include ../autoclrs.test.mk
