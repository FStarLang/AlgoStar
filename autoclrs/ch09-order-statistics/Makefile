PULSE_ROOT ?= ../../pulse
# Only include pure F* files in FSTAR_FILES for dependency analysis.
# Pulse Impl files use #lang-pulse and require the Pulse plugin for parsing;
# they are checked separately (deps are appended manually to .depend).
FSTAR_FILES = $(filter-out %Impl.fst %Impl.fsti,$(wildcard *.fst) $(wildcard *.fsti))
include $(PULSE_ROOT)/mk/test.mk
# Explicitly disable optimize_let_vc and fly_deps for this chapter — they break
# quantifier instantiation in insert_sorted (CLRS.Ch09.PartialSelectionSort.Spec.fst)
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --ext optimize_let_vc=false --ext fly_deps=false --include ../common
