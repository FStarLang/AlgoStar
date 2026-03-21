(*
   ISSUE 04: Removing an existential from inner while loop invariant causes
   "Ill-typed term" in CLRS.Ch22.DFS.Impl.fst

   MINIMAL REPRO: Not yet isolated — simplified versions don't trigger the bug.
   The issue only manifests in the full DFS code with its many existentials,
   complex predicates (stack_ok, dfs_ok, gray_ok, etc.), and deeply nested
   if-else branches after the inner loop.

   TO REPRODUCE in the actual code:

   In autoclrs/ch22-elementary-graph/CLRS.Ch22.DFS.Impl.fst, function `dfs_visit`
   (around line 940), the outer while loop has `// TODO: decreases`. To add
   `decreases (2 * SZ.v n - !time_ref)`:

   1. The inner scan loop (line ~1005) wraps `time_ref` in its invariant:
        invariant exists* ... vtime_scan ...
          R.pts_to time_ref vtime_scan **
      The scan loop doesn't modify `time_ref`, but existentially re-quantifying
      `vtime_scan` loses the equation `vtime_scan == vtime_w` (outer value).
      This makes the decreases check fail (can't prove strict decrease).

   2. The fix: capture `time_ref` before the scan loop and use a fixed value:
        let tv = !time_ref;
        while (...)
        invariant exists* ... scolor_scan sd_scan ... sscan_scan ...  // no vtime_scan
          R.pts_to time_ref tv **  // fixed, non-existential
          ...

   3. This causes "Ill-typed term" on `sum_scan_idx_upd sscan_pre_disc ...`
      (around line 1113) — a pure lemma call using a `with`-bound variable
      extracted after the inner loop:
        with sscan_pre_disc. assert (A.pts_to scan_idx sscan_pre_disc);
        sum_scan_idx_upd sscan_pre_disc (SZ.v n) (SZ.v vv) 0sz;  // <-- FAILS

   VARIATIONS TRIED (all produce the same "Ill-typed term" error):
   - Remove `vtime_scan` from existentials, use `R.pts_to time_ref tv`
   - Keep `vtime_scan` in existentials, add `vtime_scan == tv` to pure block
   - Frame `time_ref` out of the scan loop entirely (remove R.pts_to)
   - Use `with time_val. assert (R.pts_to time_ref time_val)` before loop

   The error consistently appears at `sum_scan_idx_upd` or `count_ones_lt`
   after ANY modification to the inner scan loop invariant's structure.

   WORKAROUND: Hoist the inner scan loop into a separate Pulse `fn`.

   STATUS: open — blocks adding decreases to DFS outer loop in ch22.
*)
module ISSUE_04_inner_loop_existential_removal
