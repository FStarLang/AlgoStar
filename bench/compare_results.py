#!/usr/bin/env python3
"""compare_results.py — Side-by-side comparison of two benchmark runs.

Usage:
    python3 bench/compare_results.py bench/results/baseline bench/results/uvar-fix
"""

import csv
import sys
import os
import re

def parse_wall_time(s):
    """Parse wall time string like '1:23.45' or '0:05.12' into seconds."""
    s = s.strip()
    if not s:
        return 0.0
    # Format: [h:]m:ss.cc
    parts = s.split(':')
    if len(parts) == 3:
        h, m, sec = parts
        return int(h) * 3600 + int(m) * 60 + float(sec)
    elif len(parts) == 2:
        m, sec = parts
        return int(m) * 60 + float(sec)
    else:
        return float(s)

def load_results(results_dir):
    """Load summary.csv into a dict keyed by basename."""
    csv_path = os.path.join(results_dir, "summary.csv")
    data = {}
    with open(csv_path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            # Use context__file key for uniqueness, display shortened name
            fname = row['file']
            # The key in the CSV is the full "cwd__file" path from metrics
            data[fname] = {
                'file': fname,
                'display': os.path.basename(fname),
                'exit_code': int(row['exit_code']),
                'wall_sec': parse_wall_time(row['wall_time']),
                'peak_mb': int(row['peak_kb']) / 1024.0,
            }
    return data

def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <baseline_dir> <fix_dir>")
        sys.exit(1)

    base_dir, fix_dir = sys.argv[1], sys.argv[2]
    base_label = os.path.basename(base_dir)
    fix_label = os.path.basename(fix_dir)

    base = load_results(base_dir)
    fix = load_results(fix_dir)

    # Load real build wall times
    def load_build_summary(d):
        path = os.path.join(d, "build_summary.txt")
        info = {}
        if os.path.exists(path):
            with open(path) as f:
                for line in f:
                    k, _, v = line.strip().partition('=')
                    info[k] = v
        return info

    base_summary = load_build_summary(base_dir)
    fix_summary = load_build_summary(fix_dir)

    all_files = sorted(set(base.keys()) | set(fix.keys()))

    # Header
    print(f"\n{'='*100}")
    print(f"AlgoStar Benchmark Comparison: {base_label} vs {fix_label}")
    print(f"{'='*100}")

    # --- Regressions ---
    regressions = []
    improvements = []
    for f in all_files:
        b = base.get(f)
        x = fix.get(f)
        if b and x:
            if b['exit_code'] == 0 and x['exit_code'] != 0:
                regressions.append(f)
            elif b['exit_code'] != 0 and x['exit_code'] == 0:
                improvements.append(f)

    if regressions:
        print(f"\n⚠️  PROOF REGRESSIONS ({len(regressions)} files fail with {fix_label} but pass with {base_label}):")
        for f in regressions:
            print(f"   ✗ {f}")

    if improvements:
        print(f"\n✅ NEW PASSES ({len(improvements)} files pass with {fix_label} but fail with {base_label}):")
        for f in improvements:
            print(f"   ✓ {f}")

    # --- Side-by-side table ---
    print(f"\n{'─'*120}")
    hdr = f"{'File':<45} {'Status':>8} {'Time(s)':>8} {'Mem(MB)':>8}  │ {'Status':>8} {'Time(s)':>8} {'Mem(MB)':>8}  │ {'ΔTime':>7} {'ΔMem':>7}"
    print(f"{'':45} {'── ' + base_label + ' ──':^28} │ {'── ' + fix_label + ' ──':^28} │ {'── Δ ──':^16}")
    print(hdr)
    print(f"{'─'*120}")

    total_base_time = 0
    total_fix_time = 0
    total_base_mem = 0
    total_fix_mem = 0
    both_pass_count = 0

    for f in all_files:
        b = base.get(f, {'exit_code': -1, 'wall_sec': 0, 'peak_mb': 0})
        x = fix.get(f, {'exit_code': -1, 'wall_sec': 0, 'peak_mb': 0})

        b_status = "PASS" if b['exit_code'] == 0 else ("FAIL" if b['exit_code'] > 0 else "N/A")
        x_status = "PASS" if x['exit_code'] == 0 else ("FAIL" if x['exit_code'] > 0 else "N/A")

        # Mark regressions
        marker = ""
        if f in regressions:
            marker = " ⚠️"
        elif f in improvements:
            marker = " ✅"

        dt = ""
        dm = ""
        if b['exit_code'] != -1 and x['exit_code'] != -1:
            if b['wall_sec'] > 0:
                dt_pct = (x['wall_sec'] - b['wall_sec']) / b['wall_sec'] * 100
                dt = f"{dt_pct:+.0f}%"
            if b['peak_mb'] > 0:
                dm_pct = (x['peak_mb'] - b['peak_mb']) / b['peak_mb'] * 100
                dm = f"{dm_pct:+.0f}%"

        total_base_time += b['wall_sec']
        total_fix_time += x['wall_sec']
        total_base_mem += b['peak_mb']
        total_fix_mem += x['peak_mb']
        if b['exit_code'] == 0 and x['exit_code'] == 0:
            both_pass_count += 1

        # Truncate filename
        fn = f[:44] if len(f) > 44 else f
        display = base.get(f, fix.get(f, {})).get('display', fn)
        display = display[:44] if len(display) > 44 else display

        print(f"{display:<45} {b_status:>8} {b['wall_sec']:>8.1f} {b['peak_mb']:>8.0f}  │ "
              f"{x_status:>8} {x['wall_sec']:>8.1f} {x['peak_mb']:>8.0f}  │ {dt:>7} {dm:>7}{marker}")

    # --- Summary ---
    print(f"{'─'*120}")
    print(f"\n{'='*60}")
    print(f"SUMMARY")
    print(f"{'='*60}")
    print(f"Files measured ({base_label}): {len(base)}")
    print(f"Files measured ({fix_label}):  {len(fix)}")
    print(f"Both pass:                     {both_pass_count}")
    print(f"Regressions:                   {len(regressions)}")
    print(f"New passes:                    {len(improvements)}")
    print()
    # Real build wall time
    base_btime = base_summary.get('total_seconds', '?')
    fix_btime = fix_summary.get('total_seconds', '?')
    print(f"Real build wall time ({base_label}): {base_btime}s")
    print(f"Real build wall time ({fix_label}):  {fix_btime}s")
    print()
    print(f"Sum of per-file wall times ({base_label}): {total_base_time:.0f}s (includes parallelism overlap)")
    print(f"Sum of per-file wall times ({fix_label}):  {total_fix_time:.0f}s")
    if total_base_time > 0:
        print(f"Sum-of-times change: {(total_fix_time - total_base_time) / total_base_time * 100:+.1f}%")
    print()
    print(f"Max peak memory ({base_label}): {max((d['peak_mb'] for d in base.values()), default=0):.0f} MB")
    print(f"Max peak memory ({fix_label}):  {max((d['peak_mb'] for d in fix.values()), default=0):.0f} MB")
    print(f"Median peak memory ({base_label}): {sorted(d['peak_mb'] for d in base.values())[len(base)//2] if base else 0:.0f} MB")
    print(f"Median peak memory ({fix_label}):  {sorted(d['peak_mb'] for d in fix.values())[len(fix)//2] if fix else 0:.0f} MB")

    # Top memory consumers
    print(f"\nTop 10 memory consumers ({fix_label}):")
    fix_sorted = sorted(fix.items(), key=lambda kv: kv[1]['peak_mb'], reverse=True)[:10]
    for fname, d in fix_sorted:
        b = base.get(fname, {'peak_mb': 0})
        print(f"  {fname:<50} {d['peak_mb']:>8.0f} MB  (baseline: {b['peak_mb']:>8.0f} MB)")

    # Biggest memory improvements
    print(f"\nTop 10 memory improvements ({base_label} → {fix_label}):")
    deltas = []
    for fname in all_files:
        b = base.get(fname, {'peak_mb': 0})
        x = fix.get(fname, {'peak_mb': 0})
        if b['peak_mb'] > 50:  # Only show meaningful files
            delta = b['peak_mb'] - x['peak_mb']
            deltas.append((fname, b['peak_mb'], x['peak_mb'], delta))
    deltas.sort(key=lambda t: t[3], reverse=True)
    for fname, bmem, xmem, delta in deltas[:10]:
        print(f"  {fname:<50} {bmem:>8.0f} → {xmem:>8.0f} MB  (saved {delta:>8.0f} MB)")

if __name__ == "__main__":
    main()
