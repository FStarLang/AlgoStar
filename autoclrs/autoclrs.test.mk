# autoclrs/autoclrs.test.mk — Shared C extraction and test infrastructure
#
# This file factors out the common KaRaMeL extraction, C compilation,
# and test-execution logic that every chapter Makefile duplicates.
#
# ── Usage ──────────────────────────────────────────────────────────
#
# In each chapter Makefile, set the required variables, then include:
#
#   CHAPTER_ID        = ch06
#   KRML_INPUT_FILES  = $(OUTPUT_DIR)/Foo.krml $(OUTPUT_DIR)/Bar.krml
#   KRML_BUNDLE_FLAGS = -bundle 'Foo=Foo.*'
#   EXTRACT_C_FILES   = $(EXTRACT_DIR)/Foo.c
#   include ../autoclrs.test.mk          # provides extract / test-c targets
#
# ── Required variables (must be set before including) ──────────────
#
#   CHAPTER_ID          Short name, e.g. ch06.  Used for naming only.
#   KRML_INPUT_FILES    .krml files to feed KaRaMeL.
#   KRML_BUNDLE_FLAGS   -bundle flags for KaRaMeL (always chapter-specific).
#   EXTRACT_C_FILES     .c file(s) that KaRaMeL produces.
#
# ── Optional variables (have sensible defaults) ────────────────────
#
#   EXTRACT_DIR         Where extracted C lands  (default: $(OUTPUT_DIR))
#   KRML_WARN_FLAGS     Warnings for KaRaMeL     (default: -warn-error -2-9-11-15-17)
#   KRML_EXTRA_FLAGS    Extra KaRaMeL flags       (default: empty)
#   KRML_EXTRA_INPUTS   Extra .krml inputs        (default: empty)
#   TEST_MAIN           Hand-written C driver     (default: main.c)
#   EXTRA_C_SOURCES     Extra .c files to compile (default: empty)
#   CC_EXTRA_FLAGS      Extra CFLAGS              (default: empty)
#   CC_EXTRA_INCLUDES   Extra -I dirs             (default: empty)
#   EXTRA_LINK_LIBS     Libraries for linking      (default: empty)
#   TEST_EXE_NAME       Executable name            (default: $(CHAPTER_ID)_test)

# ─── Standard defaults ─────────────────────────────────────────────

KRML_HOME         ?= ../../FStar/karamel
KRML_EXE          ?= $(KRML_HOME)/krml
EXTRACT_DIR       ?= $(OUTPUT_DIR)
KRML_WARN_FLAGS   ?= -warn-error -2-9-11-15-17
KRML_EXTRA_FLAGS  ?=
KRML_EXTRA_INPUTS ?=
TEST_MAIN         ?= main.c
EXTRA_C_SOURCES   ?=
CC_EXTRA_FLAGS    ?=
CC_EXTRA_INCLUDES ?=
EXTRA_LINK_LIBS   ?=
TEST_EXE_NAME     ?= $(CHAPTER_ID)_test

TEST_EXE           = $(EXTRACT_DIR)/$(TEST_EXE_NAME)

# Standard include paths for compiling KaRaMeL-extracted C
KRML_CC_INCLUDES = \
  -I $(KRML_HOME)/include \
  -I $(KRML_HOME)/krmllib/dist/minimal \
  -I $(KRML_HOME)/krmllib/dist/generic \
  -I $(KRML_HOME)/krmllib \
  -I $(EXTRACT_DIR) \
  -I .

# Standard C compiler flags
KRML_CC_FLAGS = \
  -std=c11 -Wall -g -fwrapv \
  -D_BSD_SOURCE -D_DEFAULT_SOURCE \
  -Wno-unused-variable -Wno-unused-parameter \
  -Wno-parentheses

# ─── Step 1: KaRaMeL  .krml → .c ──────────────────────────────────
#
# The first file in EXTRACT_C_FILES is the primary make target.
# All files are produced atomically by a single krml invocation.

__EXTRACT_PRIMARY = $(firstword $(EXTRACT_C_FILES))

$(__EXTRACT_PRIMARY): $(KRML_INPUT_FILES)
	$(call msg, "KRML", "$(CHAPTER_ID)")
	@mkdir -p $(EXTRACT_DIR)
	$(KRML_EXE) \
	  -skip-makefiles -skip-compilation -skip-linking \
	  $(KRML_WARN_FLAGS) \
	  -add-include '"krml/internal/compat.h"' \
	  $(KRML_BUNDLE_FLAGS) \
	  $(KRML_EXTRA_FLAGS) \
	  -tmpdir $(EXTRACT_DIR) \
	  $(KRML_INPUT_FILES) \
	  $(KRML_EXTRA_INPUTS)

# If KaRaMeL produces more than one .c, the extras depend on the primary.
# The @: no-op recipe prevents make from falling through to test.mk's
# implicit pattern rule for .c-from-.krml extraction.
ifneq ($(word 2,$(EXTRACT_C_FILES)),)
$(wordlist 2,$(words $(EXTRACT_C_FILES)),$(EXTRACT_C_FILES)): $(__EXTRACT_PRIMARY)
	@:
endif

# ─── Step 2: Compile + Link ───────────────────────────────────────

$(TEST_EXE): $(EXTRACT_C_FILES) $(TEST_MAIN) $(EXTRA_C_SOURCES)
	$(call msg, "CC+LINK", "$(TEST_EXE_NAME)")
	@mkdir -p $(dir $@)
	$(CC) $(KRML_CC_FLAGS) $(CC_EXTRA_FLAGS) \
	  $(KRML_CC_INCLUDES) $(CC_EXTRA_INCLUDES) \
	  -o $@ \
	  $(TEST_MAIN) \
	  $(EXTRACT_C_FILES) \
	  $(EXTRA_C_SOURCES) \
	  $(EXTRA_LINK_LIBS)

# ─── Step 3: Run ──────────────────────────────────────────────────

$(TEST_EXE).out: $(TEST_EXE)
	$(call msg, "RUN", "$(TEST_EXE_NAME)")
	./$< | tee $@

# ─── Convenience phony targets ────────────────────────────────────

.PHONY: extract test-c
extract: $(EXTRACT_C_FILES)
test-c:  $(TEST_EXE).out
