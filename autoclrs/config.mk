# autoclrs/config.mk — Shared toolchain detection for all chapter Makefiles
#
# Usage: include this file BEFORE including $(PULSE_ROOT)/mk/test.mk
#   From chapter dirs:  include ../config.mk
#   From autoclrs/:     include config.mk
#
# Detects binary install (fstar/) vs source build (FStar/) and sets:
#   PULSE_ROOT, FSTAR_EXE, KRML_HOME, STAGE3

_CONFIG_MK_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
_REPO_ROOT     := $(abspath $(_CONFIG_MK_DIR)/..)

ifneq ($(wildcard $(_REPO_ROOT)/fstar/bin/fstar.exe),)
  # Binary install
  PULSE_ROOT ?= $(_REPO_ROOT)/fstar/pulse
  ifndef FSTAR_EXE
    FSTAR_EXE := $(_REPO_ROOT)/fstar/bin/fstar.exe
  endif
  KRML_HOME  ?= $(_REPO_ROOT)/fstar/karamel
else
  # Source build
  PULSE_ROOT ?= $(_REPO_ROOT)/FStar/pulse
  ifndef FSTAR_EXE
    FSTAR_EXE := $(_REPO_ROOT)/FStar/out/bin/fstar.exe
  endif
  KRML_HOME  ?= $(_REPO_ROOT)/FStar/karamel
endif
STAGE3     ?= 1
