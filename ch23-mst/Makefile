PULSE_ROOT ?= ../pulse
include $(PULSE_ROOT)/mk/test.mk
# Undo optimize_let_vc and fly_deps — they break SizeT overflow
# reasoning in Prim.fst
OTHERFLAGS := $(subst --ext optimize_let_vc,,$(subst --ext fly_deps,,$(OTHERFLAGS))) --ext optimize_let_vc=false --ext fly_deps=false --include ../common
