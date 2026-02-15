PULSE_ROOT ?= ../../pulse
include $(PULSE_ROOT)/mk/test.mk
# Undo optimize_let_vc and fly_deps — they break modular arithmetic
# reasoning in Queue.fst dequeue proof
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --include ../common
