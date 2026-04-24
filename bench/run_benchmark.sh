#!/bin/bash
# run_benchmark.sh — Full AlgoStar benchmark for a given F* binary
#
# Usage:
#   ./bench/run_benchmark.sh <label> <fstar_exe>
#
# Example:
#   ./bench/run_benchmark.sh baseline  fstar/bin/fstar.exe
#   ./bench/run_benchmark.sh uvar-fix  /home/nswamy/FStar-uvar-fix/out/bin/fstar.exe
#
# Output: bench/results/<label>/ with per-file .metrics files and summary.csv

set -uo pipefail

LABEL="${1:?Usage: run_benchmark.sh <label> <fstar_exe>}"
FSTAR_EXE_PATH="${2:?Usage: run_benchmark.sh <label> <fstar_exe>}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RESULTS_DIR="$SCRIPT_DIR/results/$LABEL"
METRICS_DIR="$RESULTS_DIR/metrics"
WRAPPER="$SCRIPT_DIR/fstar_wrapper.sh"

# Resolve fstar.exe to absolute path
if [[ "$FSTAR_EXE_PATH" != /* ]]; then
  FSTAR_EXE_PATH="$REPO_ROOT/$FSTAR_EXE_PATH"
fi

echo "=== AlgoStar Benchmark: $LABEL ==="
echo "F* binary: $FSTAR_EXE_PATH"
echo "Results:   $RESULTS_DIR"
echo ""

# Verify the binary exists and get version
if [[ ! -x "$FSTAR_EXE_PATH" ]]; then
  echo "ERROR: $FSTAR_EXE_PATH not found or not executable" >&2
  exit 1
fi

"$FSTAR_EXE_PATH" --version 2>&1 | head -1 | tee "$RESULTS_DIR/fstar_version.txt" || true

# Setup
mkdir -p "$METRICS_DIR"
chmod +x "$WRAPPER"

# Clean build artifacts
echo ""
echo ">>> Cleaning build artifacts..."
make -C "$REPO_ROOT" clean 2>&1 | tail -2

# Record start time
echo ""
echo ">>> Starting build at $(date)"
start_epoch=$(date +%s)

# Run make with our wrapper, using -j for parallelism but capped to avoid OOM
# We set FSTAR_EXE to the wrapper, which calls the real binary
export REAL_FSTAR_EXE="$FSTAR_EXE_PATH"
export METRICS_DIR

set +e
make -C "$REPO_ROOT" \
  FSTAR_EXE="$WRAPPER" \
  -j8 \
  2>&1 | tee "$RESULTS_DIR/build.log"
build_exit=${PIPESTATUS[0]}
set -e

end_epoch=$(date +%s)
total_secs=$((end_epoch - start_epoch))

echo ""
echo ">>> Build finished at $(date) (${total_secs}s total, exit=$build_exit)"
echo "total_seconds=$total_secs" > "$RESULTS_DIR/build_summary.txt"
echo "exit_code=$build_exit" >> "$RESULTS_DIR/build_summary.txt"

# Generate summary CSV from metrics files
echo "file,exit_code,wall_time,peak_kb" > "$RESULTS_DIR/summary.csv"
for f in "$METRICS_DIR"/*.metrics; do
  [[ -f "$f" ]] || continue
  file=$(grep '^file=' "$f" | cut -d= -f2-)
  ec=$(grep '^exit_code=' "$f" | cut -d= -f2-)
  wt=$(grep '^wall_time=' "$f" | cut -d= -f2-)
  pk=$(grep '^peak_kb=' "$f" | cut -d= -f2-)
  echo "$file,$ec,$wt,$pk"
done | sort >> "$RESULTS_DIR/summary.csv"

# Count pass/fail
total=$(ls "$METRICS_DIR"/*.metrics 2>/dev/null | wc -l)
passed=$(grep -l 'exit_code=0' "$METRICS_DIR"/*.metrics 2>/dev/null | wc -l)
failed=$((total - passed))

echo ""
echo "=== Results: $LABEL ==="
echo "Total files verified: $total"
echo "Passed: $passed"
echo "Failed: $failed"
echo "Total wall time: ${total_secs}s"

# List failures if any
if [[ $failed -gt 0 ]]; then
  echo ""
  echo "--- FAILURES ---"
  for f in "$METRICS_DIR"/*.metrics; do
    ec=$(grep '^exit_code=' "$f" | cut -d= -f2-)
    if [[ "$ec" != "0" ]]; then
      file=$(grep '^file=' "$f" | cut -d= -f2-)
      echo "  FAIL: $file"
    fi
  done
fi

echo ""
echo "Full results in: $RESULTS_DIR/summary.csv"
