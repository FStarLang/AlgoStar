PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk
# Explicitly disable optimize_let_vc and fly_deps for this chapter — they break
# quantifier instantiation in insert_sorted (CLRS.Ch09.PartialSelectionSort.Spec.fst)
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --ext optimize_let_vc=false --ext fly_deps=false --include ../common
