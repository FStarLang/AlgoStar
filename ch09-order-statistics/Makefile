PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk
# Undo optimize_let_vc and fly_deps for this chapter — they break
# quantifier instantiation in insert_sorted (CLRS.Ch09.PartialSelectionSort.Spec.fst)
# Add explicit --include ../common since fly_deps is removed
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --include ../common
