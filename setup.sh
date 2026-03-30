#!/usr/bin/env bash
# setup.sh — Build F* (fstar2 branch: unified F*, Pulse, KaRaMeL)
#
# Prerequisites:
#   - OCaml (>= 4.14) with opam
#   - Z3 (>= 4.8.5, must be in PATH)
#   - GNU make, git
#
# Usage:
#   ./setup.sh          # build F* stage3 + KaRaMeL
#   ./setup.sh fstar    # build only F* stage3
#   ./setup.sh karamel  # build only KaRaMeL (requires F* already built)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FSTAR_DIR="$SCRIPT_DIR/FStar"
FSTAR_EXE="$FSTAR_DIR/out/bin/fstar.exe"
KRML_EXE="$FSTAR_DIR/karamel/krml"
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
  if [ ! -f "$FSTAR_DIR/Makefile" ]; then
    info "Initializing git submodules..."
    cd "$SCRIPT_DIR"
    git submodule update --init --recursive
  fi
  # Ensure karamel submodule is initialized within FStar
  if [ ! -f "$FSTAR_DIR/karamel/Makefile" ]; then
    info "Initializing karamel submodule..."
    cd "$FSTAR_DIR"
    git submodule update --init karamel
  fi
}

build_fstar() {
  info "Building F* stage3 (this may take 20-40 minutes)..."
  cd "$FSTAR_DIR"
  make -j"$NPROC" 3
  if [ -x "$FSTAR_EXE" ]; then
    green "F* built successfully: $FSTAR_EXE"
    "$FSTAR_EXE" --version
  else
    red "F* build failed — $FSTAR_EXE not found."
    exit 1
  fi
}

patch_karamel() {
  local patch="$SCRIPT_DIR/patches/karamel-simplify-bounds-check.patch"
  if [ -f "$patch" ]; then
    cd "$FSTAR_DIR/karamel"
    if ! git diff --quiet lib/Simplify.ml 2>/dev/null; then
      info "KaRaMeL Simplify.ml already modified, skipping patch."
    elif patch -p1 --dry-run < "$patch" >/dev/null 2>&1; then
      info "Applying KaRaMeL Simplify.ml bounds-check patch..."
      patch -p1 < "$patch"
    else
      info "KaRaMeL patch already applied or does not apply cleanly, skipping."
    fi
  fi
}

build_karamel() {
  if [ ! -x "$FSTAR_EXE" ]; then
    red "F* not built yet. Run './setup.sh fstar' first."
    exit 1
  fi
  patch_karamel
  info "Building KaRaMeL..."
  cd "$FSTAR_DIR"
  make karamel
  if [ -x "$KRML_EXE" ]; then
    green "KaRaMeL built successfully: $KRML_EXE"
  else
    red "KaRaMeL build failed — $KRML_EXE not found."
    exit 1
  fi
}

# ---- Main ----

check_prereqs
check_submodules

case "${1:-all}" in
  fstar) build_fstar ;;
  karamel) build_karamel ;;
  all)
    build_fstar
    build_karamel
    echo
    green "Setup complete. Run 'make' to verify all chapters."
    ;;
  *)
    echo "Usage: $0 [fstar|karamel|all]"
    exit 1
    ;;
esac
