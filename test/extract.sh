#!/bin/bash
# extract.sh — Extract all AutoCLRS Pulse modules to C via karamel
# Usage: ./test/extract.sh [output_dir]
#
# Steps:
#   1. Extract each module to .krml via fstar --codegen krml
#   2. Convert .krml to .c/.h via krml
#   3. Collect all .c/.h into the output directory

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
AUTOCLRS="$(cd "$SCRIPT_DIR/.." && pwd)"
PULSE_ROOT="${PULSE_ROOT:-$AUTOCLRS/../pulse}"
KRML_HOME="${KRML_HOME:-$AUTOCLRS/../karamel}"
KRML_EXE="$KRML_HOME/krml"
FSTAR_EXE="${FSTAR_EXE:-fstar.exe}"
OUTPUT_DIR="${1:-$AUTOCLRS/test/extracted}"

FSTAR_OPTS="--cache_checked_modules \
  --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
  --cmi --warn_error -321 --warn_error @247 \
  --ext optimize_let_vc --ext fly_deps \
  --include $PULSE_ROOT/out/lib/pulse \
  --codegen krml"

KRML_FLAGS="-skip-makefiles -skip-linking -warn-error -2-3-4-9-11-15-17"

mkdir -p "$OUTPUT_DIR"

echo "=== AutoCLRS C Extraction ==="
echo "Output: $OUTPUT_DIR"
echo ""

# Modules to extract (module_name:chapter_dir)
MODULES=(
    "CLRS.Ch02.InsertionSort:ch02-getting-started"
    "CLRS.Ch02.MergeSort:ch02-getting-started"
    "CLRS.Ch04.MaxSubarray:ch04-divide-conquer"
    "CLRS.Ch06.Heap:ch06-heapsort"
    "CLRS.Ch07.Quicksort.Impl:ch07-quicksort"
    "CLRS.Ch08.CountingSort:ch08-linear-sorting"
    "CLRS.Ch08.RadixSort:ch08-linear-sorting"
    "CLRS.Ch08.BucketSort:ch08-linear-sorting"
    "CLRS.Ch09.MinMax:ch09-order-statistics"
    "CLRS.Ch09.Select:ch09-order-statistics"
    "CLRS.Ch11.HashTable:ch11-hash-tables"
    "CLRS.Ch12.BST:ch12-bst"
    "CLRS.Ch15.RodCutting:ch15-dynamic-programming"
    "CLRS.Ch15.LCS:ch15-dynamic-programming"
    "CLRS.Ch15.MatrixChain:ch15-dynamic-programming"
    "CLRS.Ch16.ActivitySelection:ch16-greedy"
    "CLRS.Ch16.Huffman:ch16-greedy"
    "CLRS.Ch21.UnionFind:ch21-disjoint-sets"
    "CLRS.Ch22.DFS:ch22-elementary-graph"
    "CLRS.Ch22.TopologicalSort:ch22-elementary-graph"
    "CLRS.Ch23.Prim:ch23-mst"
    "CLRS.Ch24.BellmanFord:ch24-sssp"
    "CLRS.Ch24.Dijkstra:ch24-sssp"
    "CLRS.Ch25.FloydWarshall:ch25-apsp"
    "CLRS.Ch26.MaxFlow:ch26-max-flow"
    "CLRS.Ch28.MatrixMultiply:ch28-matrix-ops"
    "CLRS.Ch31.GCD:ch31-number-theory"
    "CLRS.Ch31.ModExp:ch31-number-theory"
    "CLRS.Ch32.RabinKarp:ch32-string-matching"
    "CLRS.Ch33.Segments:ch33-comp-geometry"
    "CLRS.Ch35.VertexCover:ch35-approximation"
)

# Step 1: Extract all modules to .krml
echo "--- Step 1: Extracting .fst → .krml ---"
# Track which chapters need BoundedIntegers
BI_CHAPTERS=()

for entry in "${MODULES[@]}"; do
    mod="${entry%%:*}"
    dir="${entry##*:}"
    checked="$AUTOCLRS/$dir/_cache/${mod}.fst.checked"
    krml_name="$(echo "$mod" | tr '.' '_')"
    krml_file="$AUTOCLRS/$dir/_output/${krml_name}.krml"

    if [ ! -f "$checked" ]; then
        echo "  SKIP $mod (not checked — run 'make' first)"
        continue
    fi

    if [ -f "$krml_file" ]; then
        echo "  HAVE $mod"
    else
        echo -n "  EXTRACT $mod ... "
        cd "$AUTOCLRS/$dir"
        $FSTAR_EXE $FSTAR_OPTS --odir _output --cache_dir _cache \
            --extract_module "$mod" "$checked" > /dev/null 2>&1
        echo "OK"
    fi

    BI_CHAPTERS+=("$dir")
done

# Extract BoundedIntegers for chapters that need it
echo ""
echo "--- Step 1b: Extracting BoundedIntegers ---"
SEEN_DIRS=()
for dir in "${BI_CHAPTERS[@]}"; do
    # Skip if already processed
    skip=0
    for seen in "${SEEN_DIRS[@]}"; do
        if [ "$seen" = "$dir" ]; then skip=1; break; fi
    done
    if [ $skip -eq 1 ]; then continue; fi
    SEEN_DIRS+=("$dir")

    bi="$AUTOCLRS/$dir/_output/Pulse_Lib_BoundedIntegers.krml"
    if [ -f "$bi" ]; then
        echo "  HAVE BoundedIntegers for $dir"
        continue
    fi

    checked=$(ls "$AUTOCLRS/$dir/_cache/"*.fst.checked 2>/dev/null | head -1)
    if [ -z "$checked" ]; then continue; fi

    echo -n "  EXTRACT BoundedIntegers for $dir ... "
    cd "$AUTOCLRS/$dir"
    $FSTAR_EXE $FSTAR_OPTS --odir _output --cache_dir _cache \
        --extract_module Pulse.Lib.BoundedIntegers "$checked" > /dev/null 2>&1 || true
    if [ -f "$bi" ]; then echo "OK"; else echo "N/A"; fi
done

# Step 2: Convert .krml → .c/.h via krml
echo ""
echo "--- Step 2: Converting .krml → .c/.h ---"
SEEN_DIRS2=()
for entry in "${MODULES[@]}"; do
    mod="${entry%%:*}"
    dir="${entry##*:}"

    # Process each chapter directory once with ALL its krml files
    skip=0
    for seen in "${SEEN_DIRS2[@]}"; do
        if [ "$seen" = "$dir" ]; then skip=1; break; fi
    done
    if [ $skip -eq 1 ]; then continue; fi
    SEEN_DIRS2+=("$dir")

    all_krmls=$(ls "$AUTOCLRS/$dir/_output/"*.krml 2>/dev/null | tr '\n' ' ')
    if [ -z "$all_krmls" ]; then continue; fi

    # Collect all module names for this directory
    dir_mods=""
    for e2 in "${MODULES[@]}"; do
        m2="${e2%%:*}"
        d2="${e2##*:}"
        if [ "$d2" = "$dir" ]; then
            if [ -n "$dir_mods" ]; then dir_mods="$dir_mods,"; fi
            dir_mods="${dir_mods}${m2}"
        fi
    done

    echo -n "  KRML $dir ... "
    # Bundle all modules together with BoundedIntegers
    $KRML_EXE $KRML_FLAGS \
        -bundle "${dir_mods}=${dir_mods},Pulse.Lib.BoundedIntegers" \
        $all_krmls -tmpdir "$AUTOCLRS/$dir/_output" > /dev/null 2>&1 || true
    echo "OK"
done

# Step 3: Collect all .c and .h files into output directory
echo ""
echo "--- Step 3: Collecting C files ---"
mkdir -p "$OUTPUT_DIR/internal"
count=0

# Collect ALL generated .c and .h files from chapter outputs (not just our module list)
for dir in $(find "$AUTOCLRS" -path "*/_output" -type d | sort); do
    chapter=$(basename $(dirname "$dir"))
    for f in "$dir"/*.h "$dir"/*.c; do
        [ -f "$f" ] || continue
        bn=$(basename "$f")
        case "$bn" in
            CLRS_*|K___*|krmlinit*)
                cp "$f" "$OUTPUT_DIR/"
                count=$((count + 1))
                ;;
        esac
    done
    # Copy internal headers
    if [ -d "$dir/internal" ]; then
        for f in "$dir/internal"/*.h; do
            [ -f "$f" ] || continue
            cp "$f" "$OUTPUT_DIR/internal/"
        done
    fi
done

# Remove duplicate bounded_int_int/bounded_int_nat definitions from extracted C files
# (these are provided by test/krmlinit.c instead)
for f in "$OUTPUT_DIR"/CLRS_*.c; do
    perl -i -0777 -pe 's/\nPulse_Lib_BoundedIntegers_bounded_int__krml_checked_int_t\nPulse_Lib_BoundedIntegers_bounded_int_int;\n/\n/g' "$f"
    perl -i -0777 -pe 's/\nPulse_Lib_BoundedIntegers_bounded_int__krml_checked_int_t\nPulse_Lib_BoundedIntegers_bounded_int_nat;\n/\n/g' "$f"
done

# Remove karamel-generated krmlinit.c (we provide our own)
rm -f "$OUTPUT_DIR/krmlinit.c"

echo "  Collected $count files to $OUTPUT_DIR"
echo ""
echo "=== Extraction complete ==="
