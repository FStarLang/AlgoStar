include ../config.mk
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

# ── Snapshot target ─────────────────────────────────────────────────
# Produces a self-contained snapshot/ directory with all extracted C/H
# files plus the minimal krmllib runtime needed to compile and run tests
# without the F*/KaRaMeL toolchain.

SNAPSHOT_DIR      = snapshot
SNAPSHOT_KRML     = $(SNAPSHOT_DIR)/krml/internal
SNAPSHOT_KRMLLIB  = $(SNAPSHOT_DIR)/krmllib
SNAPSHOT_INTERNAL = $(SNAPSHOT_DIR)/internal

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES)
	@echo "  [SNAPSHOT] Populating $(SNAPSHOT_DIR)/"
	@mkdir -p $(SNAPSHOT_KRML) $(SNAPSHOT_KRMLLIB) $(SNAPSHOT_INTERNAL)
	@# Extracted C/H files
	@cp $(EXTRACT_DIR)/CLRS_Ch10_Stack_ImplTest.c      $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch10_Stack_ImplTest.h      $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch10_Queue_ImplTest.c      $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch10_Queue_ImplTest.h      $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch10_SinglyLinkedList_ImplTest.c $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch10_SinglyLinkedList_ImplTest.h $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch10_DLL_ImplTest.c        $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch10_DLL_ImplTest.h        $(SNAPSHOT_DIR)/
	@# Internal headers
	@cp $(EXTRACT_DIR)/internal/CLRS_Ch10_DLL_ImplTest.h          $(SNAPSHOT_INTERNAL)/
	@cp $(EXTRACT_DIR)/internal/CLRS_Ch10_SinglyLinkedList_ImplTest.h $(SNAPSHOT_INTERNAL)/
	@cp $(EXTRACT_DIR)/internal/FStar_Pulse_PulseCore_Prims.h     $(SNAPSHOT_INTERNAL)/
	@# krmllib include headers
	@cp $(KRML_HOME)/include/krmllib.h                  $(SNAPSHOT_DIR)/
	@cp $(KRML_HOME)/include/krml/fstar_int.h           $(SNAPSHOT_DIR)/krml/
	@cp $(KRML_HOME)/include/krml/lowstar_endianness.h  $(SNAPSHOT_DIR)/krml/
	@cp $(KRML_HOME)/include/krml/internal/builtin.h    $(SNAPSHOT_KRML)/
	@cp $(KRML_HOME)/include/krml/internal/callconv.h   $(SNAPSHOT_KRML)/
	@cp $(KRML_HOME)/include/krml/internal/compat.h     $(SNAPSHOT_KRML)/
	@cp $(KRML_HOME)/include/krml/internal/debug.h      $(SNAPSHOT_KRML)/
	@cp $(KRML_HOME)/include/krml/internal/target.h     $(SNAPSHOT_KRML)/
	@cp $(KRML_HOME)/include/krml/internal/types.h      $(SNAPSHOT_KRML)/
	@# krmllib runtime C sources and headers
	@cp $(KRML_HOME)/krmllib/dist/generic/prims.c       $(SNAPSHOT_KRMLLIB)/
	@cp $(KRML_HOME)/krmllib/dist/generic/Prims.h       $(SNAPSHOT_KRMLLIB)/
	@cp $(KRML_HOME)/krmllib/dist/generic/fstar_int32.c $(SNAPSHOT_KRMLLIB)/
	@cp $(KRML_HOME)/krmllib/dist/generic/FStar_Int32.h $(SNAPSHOT_KRMLLIB)/
	@cp $(KRML_HOME)/krmllib/dist/minimal/FStar_UInt128.h          $(SNAPSHOT_KRMLLIB)/
	@cp $(KRML_HOME)/krmllib/dist/minimal/fstar_uint128_gcc64.h    $(SNAPSHOT_KRMLLIB)/
	@cp $(KRML_HOME)/krmllib/dist/minimal/FStar_UInt_8_16_32_64.h  $(SNAPSHOT_KRMLLIB)/
	@cp $(KRML_HOME)/krmllib/dist/minimal/LowStar_Endianness.h    $(SNAPSHOT_KRMLLIB)/
	@echo "  [SNAPSHOT] Done — run 'make -C $(SNAPSHOT_DIR)' to build and test"
