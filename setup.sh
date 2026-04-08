#!/usr/bin/env bash
# setup.sh — Set up F* for AlgoStar
#
# Two modes:
#
#   1. Binary install (recommended for most users):
#      ./setup.sh binary          # install latest nightly F* binary
#
#   2. Source build (for F* developers):
#      ./setup.sh                 # build F* stage3 + KaRaMeL from submodule
#      ./setup.sh fstar           # build only F* stage3
#      ./setup.sh karamel         # build only KaRaMeL (requires F* already built)
#
# Source build prerequisites:
#   - OCaml (>= 4.14) with opam
#   - Z3 (>= 4.8.5, must be in PATH)
#   - GNU make, git

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FSTAR_DIR="$SCRIPT_DIR/FStar"
FSTAR_EXE="$FSTAR_DIR/out/bin/fstar.exe"
KRML_EXE="$FSTAR_DIR/karamel/krml"
NPROC=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

# Binary install destination
FSTAR_BIN_DIR="$SCRIPT_DIR/fstar"

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

check_prereqs_binary() {
  local missing=0
  for cmd in curl git make; do
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

# ---- Binary install ----

install_binary() {
  info "Installing F* nightly binary to $FSTAR_BIN_DIR ..."
  curl -fsSL https://aka.ms/install-fstar | bash -s -- \
    --nightly \
    --dest "$FSTAR_BIN_DIR" \
    --no-link

  if [ ! -x "$FSTAR_BIN_DIR/bin/fstar.exe" ]; then
    red "Binary install failed — $FSTAR_BIN_DIR/bin/fstar.exe not found."
    exit 1
  fi

  # Download Pulse mk/ build infrastructure (needed by Makefiles)
  install_pulse_mk

  # Create KRML_HOME-compatible layout so existing Makefiles work unchanged
  setup_karamel_compat

  green "F* binary installed successfully."
  "$FSTAR_BIN_DIR/bin/fstar.exe" --version
  echo
  green "Setup complete. Run 'make' to verify all chapters."
}

# Download the Pulse mk/ files that all Makefiles depend on.
# These are small build-infrastructure files not included in binary packages.
install_pulse_mk() {
  local mk_dir="$FSTAR_BIN_DIR/pulse/mk"
  local base_url="https://raw.githubusercontent.com/FStarLang/FStar/master/pulse/mk"

  info "Downloading Pulse build infrastructure (mk files)..."
  mkdir -p "$mk_dir"
  for f in common.mk locate.mk test.mk krmlheader; do
    curl -fsSL "$base_url/$f" -o "$mk_dir/$f"
  done
  green "Pulse mk files installed to $mk_dir"
}

# Create a karamel/-compatible directory structure via symlinks.
# The binary install places KaRaMeL files at:
#   bin/krml, include/krml/*, lib/krml/*
# Existing Makefiles expect KRML_HOME with:
#   krml, include/*, krmllib/*
setup_karamel_compat() {
  local compat="$FSTAR_BIN_DIR/karamel"

  info "Setting up KaRaMeL compatibility layout..."
  rm -rf "$compat"
  mkdir -p "$compat"
  ln -sf ../bin/krml       "$compat/krml"
  ln -sf ../include/krml   "$compat/include"
  ln -sf ../lib/krml       "$compat/krmllib"
  green "KaRaMeL compatibility layout created at $compat"
}

# ---- Main ----

case "${1:-all}" in
  binary)
    check_prereqs_binary
    install_binary
    ;;
  fstar)
    check_prereqs
    check_submodules
    build_fstar
    ;;
  karamel)
    check_prereqs
    check_submodules
    build_karamel
    ;;
  all)
    check_prereqs
    check_submodules
    build_fstar
    build_karamel
    echo
    green "Setup complete. Run 'make' to verify all chapters."
    ;;
  *)
    echo "Usage: $0 [binary|fstar|karamel|all]"
    echo
    echo "  binary    Install F* from a pre-built nightly binary (fast)"
    echo "  fstar     Build F* stage3 from source (requires OCaml)"
    echo "  karamel   Build KaRaMeL from source (requires F* already built)"
    echo "  all       Build F* + KaRaMeL from source (default)"
    exit 1
    ;;
esac
