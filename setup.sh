#!/usr/bin/env bash
# setup.sh — Build FStar and Pulse from submodules
#
# Prerequisites:
#   - OCaml (>= 4.14) with opam
#   - Z3 (>= 4.8.5, must be in PATH)
#   - GNU make, git
#
# Usage:
#   ./setup.sh          # build both FStar and Pulse
#   ./setup.sh fstar    # build only FStar
#   ./setup.sh pulse    # build only Pulse (requires FStar already built)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FSTAR_DIR="$SCRIPT_DIR/FStar"
PULSE_DIR="$SCRIPT_DIR/pulse"
FSTAR_EXE="$FSTAR_DIR/bin/fstar.exe"
NPROC=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

red()   { printf '\033[1;31m%s\033[0m\n' "$*"; }
green() { printf '\033[1;32m%s\033[0m\n' "$*"; }
info()  { printf '\033[1;34m=> %s\033[0m\n' "$*"; }

check_prereqs() {
  local missing=0
  for cmd in ocaml opam z3 git make; do
    if ! command -v "$cmd" &>/dev/null; then
      red "Missing prerequisite: $cmd"
      missing=1
    fi
  done
  if [ "$missing" -ne 0 ]; then
    red "Please install missing prerequisites and re-run."
    exit 1
  fi
  green "All prerequisites found."
}

check_submodules() {
  if [ ! -f "$FSTAR_DIR/Makefile" ] || [ ! -f "$PULSE_DIR/Makefile" ]; then
    info "Initializing git submodules..."
    cd "$SCRIPT_DIR"
    git submodule update --init --recursive
  fi
}

build_fstar() {
  info "Building F* (this may take 10-20 minutes)..."
  cd "$FSTAR_DIR"
  make -j"$NPROC"
  if [ -x "$FSTAR_EXE" ]; then
    green "F* built successfully: $FSTAR_EXE"
    "$FSTAR_EXE" --version
  else
    red "F* build failed — $FSTAR_EXE not found."
    exit 1
  fi
}

build_pulse() {
  if [ ! -x "$FSTAR_EXE" ]; then
    red "F* not built yet. Run './setup.sh fstar' first."
    exit 1
  fi
  info "Building Pulse..."
  cd "$PULSE_DIR"
  FSTAR_EXE="$FSTAR_EXE" make -j"$NPROC"
  green "Pulse built successfully."
}

# ---- Main ----

check_prereqs
check_submodules

case "${1:-all}" in
  fstar) build_fstar ;;
  pulse) build_pulse ;;
  all)
    build_fstar
    build_pulse
    echo
    green "Setup complete. Run 'make' to verify all chapters."
    ;;
  *)
    echo "Usage: $0 [fstar|pulse|all]"
    exit 1
    ;;
esac
