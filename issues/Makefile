# Detect binary install (../fstar/) vs source build (../FStar/)
ifneq ($(wildcard $(CURDIR)/../fstar/bin/fstar.exe),)
  PULSE_ROOT ?= $(CURDIR)/../fstar/pulse
else
  PULSE_ROOT ?= ../pulse
endif
include $(PULSE_ROOT)/mk/test.mk
