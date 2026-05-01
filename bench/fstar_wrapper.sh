#!/bin/bash
# fstar_wrapper.sh — Wraps fstar.exe, logging time and memory per invocation.
#
# Usage: Set REAL_FSTAR_EXE to the actual binary, METRICS_DIR to output dir.
# The wrapper intercepts verify calls and records metrics.

set -uo pipefail

REAL="${REAL_FSTAR_EXE:?Set REAL_FSTAR_EXE}"
METRICS="${METRICS_DIR:?Set METRICS_DIR}"
mkdir -p "$METRICS"

# For --dep invocations, just pass through without wrapping
for arg in "$@"; do
  if [[ "$arg" == "--dep" ]]; then
    exec "$REAL" "$@"
  fi
done

# Find the main file being checked (last .fst or .fsti argument)
main_file=""
for arg in "$@"; do
  if [[ "$arg" == *.fst || "$arg" == *.fsti ]]; then
    main_file="$arg"
  fi
done

# If no .fst/.fsti found, pass through
if [[ -z "$main_file" ]]; then
  exec "$REAL" "$@"
fi

# Create a unique metrics key using CWD + filename (avoids collisions on common files)
cwd_tag=$(pwd | sed "s|.*/autoclrs/||" | tr '/' '_')
safe_name=$(echo "${cwd_tag}__${main_file}" | tr '/' '_' | tr ' ' '_')
metrics_file="$METRICS/${safe_name}.metrics"

# Run with /usr/bin/time -v, capturing its output
time_output=$(mktemp)
/usr/bin/time -v -o "$time_output" "$REAL" "$@"
exit_code=$?

wall_sec=$(grep "Elapsed (wall clock)" "$time_output" 2>/dev/null | sed 's/.*: //')
peak_kb=$(grep "Maximum resident" "$time_output" 2>/dev/null | awk '{print $NF}')

# Write metrics
{
  echo "file=$main_file"
  echo "exit_code=$exit_code"
  echo "wall_time=$wall_sec"
  echo "peak_kb=${peak_kb:-0}"
} > "$metrics_file"

rm -f "$time_output"
exit $exit_code
