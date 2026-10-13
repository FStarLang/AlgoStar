include ../config.mk
OTHERFLAGS += --include ../common
include $(PULSE_ROOT)/mk/test.mk

# ── C extraction and test targets ──────────────────────────────────
CHAPTER_ID        = ch07
EXTRACT_DIR       = _output/c

KRML_INPUT_FILES  = _output/CLRS_Ch07_Quicksort_ImplTest.krml \
                    _output/CLRS_Ch07_Quicksort_Impl.krml \
                    _output/CLRS_Ch07_Partition_Impl.krml \
                    _output/CLRS_Ch07_Partition_ImplTest.krml
KRML_BUNDLE_FLAGS = -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims'
KRML_WARN_FLAGS   = -warn-error -2-9-11-15-17
KRML_EXTRA_FLAGS  =
EXTRACT_C_FILES   = $(EXTRACT_DIR)/CLRS_Ch07_Quicksort_Impl.c \
                    $(EXTRACT_DIR)/CLRS_Ch07_Quicksort_ImplTest.c \
                    $(EXTRACT_DIR)/CLRS_Ch07_Partition_Impl.c \
                    $(EXTRACT_DIR)/CLRS_Ch07_Partition_ImplTest.c
EXTRA_C_SOURCES   = fstar_support.c \
                    $(KRML_HOME)/krmllib/dist/generic/prims.c
CC_EXTRA_FLAGS    = -include fstar_support.h
TEST_EXE_NAME     = quicksort_test.exe

include ../autoclrs.test.mk

# ── Snapshot target ─────────────────────────────────────────────────
# Creates a self-contained snapshot/ directory with all extracted and
# handwritten C code plus the minimal krmllib headers needed to build
# without an F*/KaRaMeL installation.

SNAPSHOT_DIR = snapshot

.PHONY: snapshot
snapshot: $(EXTRACT_C_FILES)
	$(call msg, "SNAPSHOT", "$(CHAPTER_ID)")
	@rm -rf $(SNAPSHOT_DIR)
	@mkdir -p $(SNAPSHOT_DIR)/internal
	@mkdir -p $(SNAPSHOT_DIR)/krmllib/krml/internal
	@# ── Copy KaRaMeL-generated C files ──
	@cp $(EXTRACT_DIR)/CLRS_Ch07_Partition_Impl.c    $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch07_Partition_Impl.h    $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch07_Partition_ImplTest.c $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch07_Partition_ImplTest.h $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch07_Quicksort_Impl.c    $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch07_Quicksort_Impl.h    $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch07_Quicksort_ImplTest.c $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/CLRS_Ch07_Quicksort_ImplTest.h $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/internal/CLRS_Ch07_Quicksort_Impl.h      $(SNAPSHOT_DIR)/internal/
	@cp $(EXTRACT_DIR)/internal/FStar_Pulse_PulseCore_Prims.h    $(SNAPSHOT_DIR)/internal/
	@# ── Copy handwritten files (with banner already present, or add one) ──
	@cp main.c            $(SNAPSHOT_DIR)/
	@cp fstar_support.c   $(SNAPSHOT_DIR)/
	@cp fstar_support.h   $(SNAPSHOT_DIR)/
	@# ── Copy krmllib runtime headers ──
	@cp $(KRML_HOME)/include/krmllib.h                       $(SNAPSHOT_DIR)/krmllib/
	@cp $(KRML_HOME)/include/krml/fstar_int.h                $(SNAPSHOT_DIR)/krmllib/krml/
	@cp $(KRML_HOME)/include/krml/lowstar_endianness.h       $(SNAPSHOT_DIR)/krmllib/krml/
	@cp $(KRML_HOME)/include/krml/c_endianness.h             $(SNAPSHOT_DIR)/krmllib/krml/
	@cp $(KRML_HOME)/include/krml/internal/compat.h          $(SNAPSHOT_DIR)/krmllib/krml/internal/
	@cp $(KRML_HOME)/include/krml/internal/target.h          $(SNAPSHOT_DIR)/krmllib/krml/internal/
	@cp $(KRML_HOME)/include/krml/internal/types.h           $(SNAPSHOT_DIR)/krmllib/krml/internal/
	@cp $(KRML_HOME)/include/krml/internal/builtin.h         $(SNAPSHOT_DIR)/krmllib/krml/internal/
	@cp $(KRML_HOME)/include/krml/internal/callconv.h        $(SNAPSHOT_DIR)/krmllib/krml/internal/
	@cp $(KRML_HOME)/include/krml/internal/debug.h           $(SNAPSHOT_DIR)/krmllib/krml/internal/
	@# ── Copy krmllib dist files (prims.c and its headers) ──
	@cp $(KRML_HOME)/krmllib/dist/generic/prims.c            $(SNAPSHOT_DIR)/krmllib/
	@cp $(KRML_HOME)/krmllib/dist/generic/Prims.h            $(SNAPSHOT_DIR)/krmllib/
	@cp $(KRML_HOME)/krmllib/dist/generic/FStar_Int32.h      $(SNAPSHOT_DIR)/krmllib/
	@# ── Copy krmllib/dist/minimal (uint128 and utility headers) ──
	@cp $(KRML_HOME)/krmllib/dist/minimal/*.h $(SNAPSHOT_DIR)/krmllib/
	@# ── Copy snapshot Makefile ──
	@cp snapshot.Makefile $(SNAPSHOT_DIR)/Makefile
	@echo "Snapshot created in $(SNAPSHOT_DIR)/"
