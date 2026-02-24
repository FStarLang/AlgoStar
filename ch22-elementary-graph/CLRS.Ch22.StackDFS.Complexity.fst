(*
   Stack-based Depth-First Search with Complexity Bound - CLRS §22.3
   
   This version proves that stack-based DFS on an adjacency matrix
   performs at most 2 * n² operations, where n is the number of vertices.
   
   We count:
   1. One tick per outer loop iteration (checking if vertex is white): n iterations
   2. One tick per neighbor check (n checks per vertex = n² total)
   
   Total: n + n² ≤ 2 * n² ticks (for n ≥ 1)
   
   Uses GhostReference.ref nat for the tick counter — fully erased at runtime.
   
   All assume_ calls eliminated: fully verified.
*)

module CLRS.Ch22.StackDFS.Complexity
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.WithPure
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module ML = FStar.Math.Lemmas
module S = CLRS.Ch22.StackDFS

(* ========== Ghost tick ========== *)

let incr_nat (n: erased nat) : erased nat = hide (Prims.op_Addition (reveal n) 1)

ghost
fn tick (ctr: GR.ref nat) (#n: erased nat)
  requires GR.pts_to ctr n
  ensures  GR.pts_to ctr (incr_nat n)
{
  GR.(ctr := incr_nat n)
}

(* ========== Complexity arithmetic lemma ========== *)

let lemma_dfs_bound_correct (outer_count inner_count n: nat)
  : Lemma (requires n >= 1 /\ outer_count <= n /\ inner_count <= n * n)
          (ensures outer_count + inner_count <= 2 * (n * n))
  = assert (outer_count <= n);
    assert (n <= n * n);
    assert (outer_count + inner_count <= n + n * n);
    assert (n + n * n <= n * n + n * n);
    assert (n * n + n * n == 2 * (n * n))

(* ========== Arithmetic helpers for SZ.fits ========== *)
let fits_product_smaller (a b c d: nat)
  : Lemma (requires c < a /\ d <= b /\ SZ.fits (a * b))
          (ensures SZ.fits (c * b) /\ SZ.fits (c * b + d))
  = assert (c * b <= a * b);
    assert (c * b + d <= a * b)

let fits_le (x y: nat)
  : Lemma (requires x <= y /\ SZ.fits y)
          (ensures SZ.fits x)
  = ()

(* ========== Graph specification ========== *)

let has_edge (adj: Seq.seq int) (n: nat) (u v: nat) : prop =
  u < n /\ v < n /\ u * n + v < Seq.length adj /\ Seq.index adj (u * n + v) <> 0

let rec reachable_in (adj: Seq.seq int) (n: nat) (source v: nat) (steps: nat)
  : Tot prop (decreases steps)
  = if steps = 0 then v == source
    else (exists (u: nat). u < n /\ reachable_in adj n source u (steps - 1) /\ has_edge adj n u v)

(* ========== sum_scan_idx: sum of scan_idx values for complexity accounting ========== *)

let rec sum_scan_idx (sscan: Seq.seq SZ.t) (k: nat{k <= Seq.length sscan})
  : Tot nat (decreases k)
  = if k = 0 then 0
    else SZ.v (Seq.index sscan (k - 1)) + sum_scan_idx sscan (k - 1)

let rec sum_scan_idx_bound (sscan: Seq.seq SZ.t) (k: nat{k <= Seq.length sscan}) (n: nat)
  : Lemma (requires forall (j:nat). j < k ==> SZ.v (Seq.index sscan j) <= n)
          (ensures sum_scan_idx sscan k <= k * n)
          (decreases k)
  = if k = 0 then ()
    else sum_scan_idx_bound sscan (k - 1) n

let rec sum_scan_idx_upd (sscan: Seq.seq SZ.t) (k: nat{k <= Seq.length sscan}) (j: nat) (v: SZ.t)
  : Lemma (requires j < Seq.length sscan)
          (ensures Seq.length (Seq.upd sscan j v) == Seq.length sscan /\
                   (j < k ==> sum_scan_idx (Seq.upd sscan j v) k == 
                              sum_scan_idx sscan k - SZ.v (Seq.index sscan j) + SZ.v v) /\
                   (j >= k ==> sum_scan_idx (Seq.upd sscan j v) k == sum_scan_idx sscan k))
          (decreases k)
  = if k = 0 then ()
    else begin
      assert (Seq.index (Seq.upd sscan j v) (k-1) == (if j = k-1 then v else Seq.index sscan (k-1)));
      sum_scan_idx_upd sscan (k - 1) j v
    end

let rec sum_scan_idx_all_zero (sscan: Seq.seq SZ.t) (k: nat{k <= Seq.length sscan})
  : Lemma (requires forall (j:nat). j < k ==> SZ.v (Seq.index sscan j) == 0)
          (ensures sum_scan_idx sscan k == 0)
          (decreases k)
  = if k = 0 then ()
    else sum_scan_idx_all_zero sscan (k - 1)

(* ========== Helper: discover a WHITE vertex v from vertex u ========== *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn discover_vertex_dfs
  (color: A.array int) (d: A.array int) (pred: A.array int)
  (stack_data: A.array SZ.t) (stack_top: ref SZ.t)
  (scan_idx: A.array SZ.t)
  (time_ref: ref int)
  (ctr: GR.ref nat)
  (u: SZ.t) (vv: SZ.t) (n: SZ.t)
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
  (#vc: erased nat)
  requires
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    GR.pts_to ctr vc **
    with_pure (
      SZ.v vv < SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v vtop < SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sd == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sstack == SZ.v n /\
      Seq.length sscan == SZ.v n /\
      vtime >= 0 /\
      Seq.index scolor (SZ.v vv) == 0 /\
      SZ.v (Seq.index sscan (SZ.v vv)) == 0 /\
      S.stack_ok scolor sstack (SZ.v n) (SZ.v vtop) /\
      S.scan_ok sscan (SZ.v n)
    )
  ensures exists* scolor' sd' spred' sstack' sscan' vtop' vtime'.
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    GR.pts_to ctr vc **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sd' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\
      Seq.length sscan' == SZ.v n /\
      SZ.v vtop' <= SZ.v n /\
      SZ.v vtop' > SZ.v vtop /\
      vtime' == vtime + 1 /\
      scolor' == Seq.upd scolor (SZ.v vv) 1 /\
      sd' == Seq.upd sd (SZ.v vv) (vtime + 1) /\
      S.stack_ok scolor' sstack' (SZ.v n) (SZ.v vtop') /\
      S.scan_ok sscan' (SZ.v n) /\
      sum_scan_idx sscan' (SZ.v n) == sum_scan_idx sscan (SZ.v n)
    )
{
  // time++
  let t = !time_ref;
  time_ref := t + 1;
  // v.d = time
  A.op_Array_Assignment d vv (t + 1);
  // v.color = GRAY
  S.count_ones_upd_to_one scolor (SZ.v n) (SZ.v vv);
  A.op_Array_Assignment color vv 1;
  // v.pi = u
  A.op_Array_Assignment pred vv (SZ.v u);
  // scan_idx[vv] = 0 (already 0 by white_scan_zero precondition)
  sum_scan_idx_upd sscan (SZ.v n) (SZ.v vv) 0sz;
  A.op_Array_Assignment scan_idx vv 0sz;
  // PUSH(stack, v)
  let top = !stack_top;
  A.op_Array_Assignment stack_data top vv;
  stack_top := SZ.add top 1sz
}
#pop-options

(* ========== Helper: finish a vertex u ========== *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn finish_vertex
  (color: A.array int) (f: A.array int)
  (stack_data: A.array SZ.t)
  (stack_top: ref SZ.t)
  (time_ref: ref int)
  (u: SZ.t) (n: SZ.t)
  (#scolor: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
  requires
    A.pts_to color scolor **
    A.pts_to f sf **
    A.pts_to stack_data sstack **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    with_pure (
      SZ.v u < SZ.v n /\
      SZ.v vtop > 0 /\
      SZ.v vtop <= SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sf == SZ.v n /\
      Seq.length sstack == SZ.v n /\
      vtime >= 0 /\
      Seq.index scolor (SZ.v u) == 1 /\
      SZ.v (Seq.index sstack (SZ.v vtop - 1)) == SZ.v u /\
      S.stack_ok scolor sstack (SZ.v n) (SZ.v vtop)
    )
  ensures exists* scolor' sf' vtop' vtime'.
    A.pts_to color scolor' **
    A.pts_to f sf' **
    A.pts_to stack_data sstack **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sf' == SZ.v n /\
      SZ.v vtop' < SZ.v vtop /\
      SZ.v vtop' <= SZ.v n /\
      vtime' > vtime /\
      scolor' == Seq.upd scolor (SZ.v u) 2 /\
      sf' == Seq.upd sf (SZ.v u) (vtime + 1) /\
      S.stack_ok scolor' sstack (SZ.v n) (SZ.v vtop')
    )
{
  // u.color = BLACK
  S.count_ones_upd_from_one scolor (SZ.v n) (SZ.v u) 2;
  A.op_Array_Assignment color u 2;
  // time++
  let t = !time_ref;
  time_ref := t + 1;
  // u.f = time
  A.op_Array_Assignment f u (t + 1);
  // POP(stack)
  let top = !stack_top;
  stack_top := SZ.sub top 1sz
}
#pop-options

(* ========== Helper: perform DFS-VISIT for a single white vertex ========== *)

#push-options "--z3rlimit 600 --fuel 2 --ifuel 1"
fn dfs_visit
  (adj: A.array int)
  (n: SZ.t)
  (vs: SZ.t)
  (color: A.array int)
  (d: A.array int)
  (f: A.array int)
  (pred: A.array int)
  (stack_data: A.array SZ.t)
  (scan_idx: A.array SZ.t)
  (stack_top: ref SZ.t)
  (time_ref: ref int)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
  (#vc: erased nat)
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to f sf **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    GR.pts_to ctr vc **
    with_pure (
      SZ.v vs < SZ.v n /\ SZ.v n > 0 /\ SZ.v vtop < SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\ Seq.length sd == SZ.v n /\
      Seq.length sf == SZ.v n /\ Seq.length spred == SZ.v n /\
      Seq.length sstack == SZ.v n /\ Seq.length sscan == SZ.v n /\
      vtime >= 0 /\ SZ.fits (SZ.v n * SZ.v n) /\
      Seq.index scolor (SZ.v vs) == 0 /\
      S.stack_ok scolor sstack (SZ.v n) (SZ.v vtop) /\
      S.scan_ok sscan (SZ.v n) /\
      S.dfs_ok scolor sd sf (SZ.v n) /\
      S.gray_ok scolor sd (SZ.v n) vtime /\
      S.nonwhite_below scolor (SZ.v vs) /\
      (* WHITE vertices have scan_idx == 0 *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor j == 0 ==> SZ.v (Seq.index sscan j) == 0))
    )
  ensures exists* scolor' sd' sf' spred' sstack' sscan' vtop' vtime' (vc': nat).
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to f sf' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    GR.pts_to ctr vc' **
    pure (
      Seq.length scolor' == SZ.v n /\ Seq.length sd' == SZ.v n /\
      Seq.length sf' == SZ.v n /\ Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\ Seq.length sscan' == SZ.v n /\
      SZ.v vtop' == 0 /\ vtime' >= vtime /\
      S.stack_ok scolor' sstack' (SZ.v n) (SZ.v vtop') /\
      S.scan_ok sscan' (SZ.v n) /\
      S.dfs_ok scolor' sd' sf' (SZ.v n) /\
      S.nonwhite_below scolor' (SZ.v vs + 1) /\
      (* Complexity: ticks == scan work done *)
      vc' + sum_scan_idx sscan (SZ.v n) == reveal vc + sum_scan_idx sscan' (SZ.v n) /\
      (* WHITE vertices still have scan_idx == 0 *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor' j == 0 ==> SZ.v (Seq.index sscan' j) == 0))
    )
{
  // Discover vs (no tick -- scan ticks suffice for complexity bound)
  let t = !time_ref;
  time_ref := t + 1;
  A.op_Array_Assignment d vs (t + 1);
  S.count_ones_upd_to_one scolor (SZ.v n) (SZ.v vs);
  A.op_Array_Assignment color vs 1;      // GRAY
  A.op_Array_Assignment pred vs (-1);    // NIL
  // scan_idx[vs] = 0 (already 0 since vs is WHITE, by white_scan_zero)
  sum_scan_idx_upd sscan (SZ.v n) (SZ.v vs) 0sz;
  A.op_Array_Assignment scan_idx vs 0sz;
  
  // PUSH(stack, vs)
  let top = !stack_top;
  A.op_Array_Assignment stack_data top vs;
  stack_top := SZ.add top 1sz;

  // Establish DFS tracking after inline discover
  S.discover_preserves_tracking scolor sd sf (SZ.v n) (SZ.v vs) t;
  S.discover_preserves_nonwhite scolor (SZ.v vs) (SZ.v vs);

  // Process stack
  while (
    let vtop = !stack_top;
    SZ.gt vtop 0sz
  )
  invariant exists* vtop_w vtime_w scolor_w sd_w sf_w spred_w sstack_w sscan_w (vc_w: nat).
    R.pts_to stack_top vtop_w **
    R.pts_to time_ref vtime_w **
    A.pts_to adj sadj **
    A.pts_to color scolor_w **
    A.pts_to d sd_w **
    A.pts_to f sf_w **
    A.pts_to pred spred_w **
    A.pts_to stack_data sstack_w **
    A.pts_to scan_idx sscan_w **
    GR.pts_to ctr vc_w **
    pure (
      SZ.v vs < SZ.v n /\
      Seq.length scolor_w == SZ.v n /\ Seq.length sd_w == SZ.v n /\
      Seq.length sf_w == SZ.v n /\ Seq.length spred_w == SZ.v n /\
      Seq.length sstack_w == SZ.v n /\ Seq.length sscan_w == SZ.v n /\
      vtime_w >= 0 /\ vtime_w >= vtime /\
      SZ.fits (SZ.v n * SZ.v n) /\
      S.stack_ok scolor_w sstack_w (SZ.v n) (SZ.v vtop_w) /\
      S.scan_ok sscan_w (SZ.v n) /\
      S.dfs_ok scolor_w sd_w sf_w (SZ.v n) /\
      S.gray_ok scolor_w sd_w (SZ.v n) vtime_w /\
      Seq.index scolor_w (SZ.v vs) <> 0 /\
      S.nonwhite_below scolor_w (SZ.v vs) /\
      (* Complexity tracking *)
      vc_w + sum_scan_idx sscan (SZ.v n) == reveal vc + sum_scan_idx sscan_w (SZ.v n) /\
      (* WHITE vertices have scan_idx == 0 *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor_w j == 0 ==> SZ.v (Seq.index sscan_w j) == 0))
    )
  {
    // u = PEEK(stack)
    let top = !stack_top;
    let u_idx: SZ.t = SZ.sub top 1sz;
    let u: SZ.t = A.op_Array_Access stack_data u_idx;
    
    assert (pure (SZ.v u < SZ.v n));

    // Get current scan position for u
    let scan_pos: SZ.t = A.op_Array_Access scan_idx u;
    
    assert (pure (SZ.v scan_pos <= SZ.v n));
    fits_product_smaller (SZ.v n) (SZ.v n) (SZ.v u) (SZ.v scan_pos);

    // Try to find next WHITE neighbor starting from scan_pos
    let mut found_white: bool = false;
    let mut next_v: SZ.t = 0sz;

    let mut scan: SZ.t = scan_pos;
    while (!scan <^ n && !found_white)
    invariant exists* vscan vfound vnext vtime_scan scolor_scan sd_scan sf_scan spred_scan sstack_scan sscan_scan (vc_scan: nat).
      R.pts_to stack_top top **
      R.pts_to time_ref vtime_scan **
      R.pts_to scan vscan **
      R.pts_to found_white vfound **
      R.pts_to next_v vnext **
      A.pts_to adj sadj **
      A.pts_to color scolor_scan **
      A.pts_to d sd_scan **
      A.pts_to f sf_scan **
      A.pts_to pred spred_scan **
      A.pts_to stack_data sstack_scan **
      A.pts_to scan_idx sscan_scan **
      GR.pts_to ctr vc_scan **
      pure (
        SZ.v vscan <= SZ.v n /\
        SZ.v u < SZ.v n /\ SZ.v top <= SZ.v n /\
        Seq.length sadj == SZ.v n * SZ.v n /\
        Seq.length scolor_scan == SZ.v n /\ Seq.length sd_scan == SZ.v n /\
        Seq.length sf_scan == SZ.v n /\ Seq.length spred_scan == SZ.v n /\
        Seq.length sstack_scan == SZ.v n /\ Seq.length sscan_scan == SZ.v n /\
        vtime_scan >= 0 /\ vtime_scan >= vtime /\
        SZ.fits (SZ.v u * SZ.v n) /\
        SZ.fits (SZ.v u * SZ.v n + SZ.v vscan) /\
        (vfound ==> SZ.v vnext < SZ.v n) /\
        (vfound ==> Seq.index scolor_scan (SZ.v vnext) == 0) /\
        Seq.index scolor_scan (SZ.v u) == 1 /\
        SZ.v (Seq.index sstack_scan (SZ.v top - 1)) == SZ.v u /\
        S.stack_ok scolor_scan sstack_scan (SZ.v n) (SZ.v top) /\
        S.scan_ok sscan_scan (SZ.v n) /\
        S.dfs_ok scolor_scan sd_scan sf_scan (SZ.v n) /\
        S.gray_ok scolor_scan sd_scan (SZ.v n) vtime_scan /\
        Seq.index scolor_scan (SZ.v vs) <> 0 /\
        S.nonwhite_below scolor_scan (SZ.v vs) /\
        (* Complexity: scan ticks == scan position advancement *)
        vc_scan + sum_scan_idx sscan (SZ.v n) + SZ.v scan_pos ==
          reveal vc + sum_scan_idx sscan_scan (SZ.v n) + SZ.v vscan /\
        SZ.v (Seq.index sscan_scan (SZ.v u)) == SZ.v scan_pos /\
        (* WHITE scan zero preserved *)
        (forall (j:nat). j < SZ.v n ==> (Seq.index scolor_scan j == 0 ==> SZ.v (Seq.index sscan_scan j) == 0))
      )
    {
      let vscan = !scan;

      // Tick for edge check
      tick ctr;

      // Check edge (u, vscan) and color[vscan]
      let offset: SZ.t = SZ.mul u n;
      let idx: SZ.t = SZ.add offset vscan;
      S.product_strict_bound (SZ.v n) (SZ.v n) (SZ.v u) (SZ.v vscan);
      let has_edge_val: int = A.op_Array_Access adj idx;

      let cvscan: int = A.op_Array_Access color vscan;

      if (has_edge_val <> 0 && cvscan = 0) {
        found_white := true;
        next_v := vscan
      };

      fits_le (SZ.v vscan + 1) (SZ.v n * SZ.v n);
      fits_product_smaller (SZ.v n) (SZ.v n) (SZ.v u) (SZ.v vscan + 1);
      scan := SZ.add vscan 1sz
    };

    // Update scan_idx[u] to where we stopped
    let final_scan = !scan;
    // Record old sum for complexity accounting
    with sscan_before_upd. assert (A.pts_to scan_idx sscan_before_upd);
    with vc_after_scan. assert (GR.pts_to ctr vc_after_scan);
    sum_scan_idx_upd sscan_before_upd (SZ.v n) (SZ.v u) final_scan;
    A.op_Array_Assignment scan_idx u final_scan;

    let found = !found_white;
    if (found) {
      // Found WHITE neighbor - discover it (inlined to preserve complexity facts)
      let vv = !next_v;
      assert (pure (SZ.v vv < SZ.v n));
      
      with scolor_now. assert (A.pts_to color scolor_now);
      with sd_now. assert (A.pts_to d sd_now);
      with sf_now. assert (A.pts_to f sf_now);
      with vtime_now. assert (R.pts_to time_ref vtime_now);
      // count_ones == top, and scolor_now[vv] == 0 (WHITE, not GRAY)
      // so count_ones < n, hence top < n
      S.count_ones_lt scolor_now (SZ.v n) (SZ.v vv);
      
      // Inline discover_vertex_dfs
      let td = !time_ref;
      time_ref := td + 1;
      A.op_Array_Assignment d vv (td + 1);
      S.count_ones_upd_to_one scolor_now (SZ.v n) (SZ.v vv);
      A.op_Array_Assignment color vv 1;
      A.op_Array_Assignment pred vv (SZ.v u);
      // scan_idx[vv] = 0 (already 0 by white_scan_zero)
      with sscan_pre_disc. assert (A.pts_to scan_idx sscan_pre_disc);
      sum_scan_idx_upd sscan_pre_disc (SZ.v n) (SZ.v vv) 0sz;
      A.op_Array_Assignment scan_idx vv 0sz;
      let topd = !stack_top;
      A.op_Array_Assignment stack_data topd vv;
      stack_top := SZ.add topd 1sz;
      // Reestablish DFS tracking
      S.discover_preserves_tracking scolor_now sd_now sf_now (SZ.v n) (SZ.v vv) vtime_now;
      S.discover_preserves_nonwhite scolor_now (SZ.v vv) (SZ.v vs)
    } else {
      // No more WHITE neighbors - finish u (inlined)
      with scolor_now. assert (A.pts_to color scolor_now);
      with sd_now. assert (A.pts_to d sd_now);
      with sf_now. assert (A.pts_to f sf_now);
      with vtime_now. assert (R.pts_to time_ref vtime_now);
      // Inline finish_vertex
      S.count_ones_upd_from_one scolor_now (SZ.v n) (SZ.v u) 2;
      A.op_Array_Assignment color u 2;
      let tf = !time_ref;
      time_ref := tf + 1;
      A.op_Array_Assignment f u (tf + 1);
      let topf = !stack_top;
      stack_top := SZ.sub topf 1sz;
      // Reestablish DFS tracking
      S.finish_preserves_tracking scolor_now sd_now sf_now (SZ.v n) (SZ.v u) vtime_now;
      S.finish_preserves_nonwhite scolor_now (SZ.v u) (SZ.v vs)
    }
  };
  
  // After the while loop, restore outer invariant shape
  with scolor_after. assert (A.pts_to color scolor_after);
  with sd_after. assert (A.pts_to d sd_after);
  with sf_after. assert (A.pts_to f sf_after);
  with spred_after. assert (A.pts_to pred spred_after);
  with sstack_after. assert (A.pts_to stack_data sstack_after);
  with sscan_after. assert (A.pts_to scan_idx sscan_after);
  with vtop_after. assert (R.pts_to stack_top vtop_after);
  with vtime_after. assert (R.pts_to time_ref vtime_after);
  with vc_final. assert (GR.pts_to ctr vc_final);
  
  assert (pure (SZ.v vtop_after == 0));
  ()
}
#pop-options

(* ========== Helper: conditionally perform DFS-VISIT if vertex is WHITE ========== *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn maybe_dfs_visit
  (adj: A.array int)
  (n: SZ.t)
  (vs: SZ.t)
  (cv: int)
  (color: A.array int)
  (d: A.array int)
  (f: A.array int)
  (pred: A.array int)
  (stack_data: A.array SZ.t)
  (scan_idx: A.array SZ.t)
  (stack_top: ref SZ.t)
  (time_ref: ref int)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
  (#vc: erased nat)
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to f sf **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    GR.pts_to ctr vc **
    with_pure (
      SZ.v vs < SZ.v n /\ SZ.v n > 0 /\ SZ.v vtop == 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\ Seq.length sd == SZ.v n /\
      Seq.length sf == SZ.v n /\ Seq.length spred == SZ.v n /\
      Seq.length sstack == SZ.v n /\ Seq.length sscan == SZ.v n /\
      vtime >= 0 /\ SZ.fits (SZ.v n * SZ.v n) /\
      cv == Seq.index scolor (SZ.v vs) /\
      S.stack_ok scolor sstack (SZ.v n) (SZ.v vtop) /\
      S.scan_ok sscan (SZ.v n) /\
      S.dfs_ok scolor sd sf (SZ.v n) /\
      S.nonwhite_below scolor (SZ.v vs) /\
      (* WHITE vertices have scan_idx == 0 *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor j == 0 ==> SZ.v (Seq.index sscan j) == 0))
    )
  ensures exists* scolor' sd' sf' spred' sstack' sscan' vtop' vtime' (vc': nat).
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to f sf' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    GR.pts_to ctr vc' **
    pure (
      Seq.length scolor' == SZ.v n /\ Seq.length sd' == SZ.v n /\
      Seq.length sf' == SZ.v n /\ Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\ Seq.length sscan' == SZ.v n /\
      SZ.v vtop' == 0 /\ vtime' >= vtime /\
      S.stack_ok scolor' sstack' (SZ.v n) (SZ.v vtop') /\
      S.scan_ok sscan' (SZ.v n) /\
      S.dfs_ok scolor' sd' sf' (SZ.v n) /\
      S.nonwhite_below scolor' (SZ.v vs + 1) /\
      (* Complexity: ticks == scan work *)
      vc' + sum_scan_idx sscan (SZ.v n) == reveal vc + sum_scan_idx sscan' (SZ.v n) /\
      (* WHITE scan zero preserved *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor' j == 0 ==> SZ.v (Seq.index sscan' j) == 0))
    )
{
  if (cv = 0) {
    // vtop == 0 ⟹ count_ones == 0 ⟹ no GRAY vertices ⟹ gray_ok vacuously
    S.no_gray_implies_gray_ok scolor sd (SZ.v n) vtime;
    dfs_visit adj n vs color d f pred stack_data scan_idx stack_top time_ref ctr
  }
}
#pop-options

(* ========== Main stack-based DFS with complexity tracking ========== *)

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
fn stack_dfs_complexity
  (adj: A.array int)
  (n: SZ.t)
  (color: A.array int)
  (d: A.array int)
  (f: A.array int)
  (pred: A.array int)
  (stack_data: A.array SZ.t)
  (scan_idx: A.array SZ.t)
  (ctr: GR.ref nat)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#c0: erased nat)
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to f sf **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    GR.pts_to ctr c0 **
    pure (
      SZ.v n > 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length sadj <= A.length adj /\
      Seq.length scolor == SZ.v n /\
      Seq.length scolor <= A.length color /\
      Seq.length sd == SZ.v n /\
      Seq.length sd <= A.length d /\
      Seq.length sf == SZ.v n /\
      Seq.length sf <= A.length f /\
      Seq.length spred == SZ.v n /\
      Seq.length spred <= A.length pred /\
      Seq.length sstack == SZ.v n /\
      Seq.length sstack <= A.length stack_data /\
      Seq.length sscan == SZ.v n /\
      Seq.length sscan <= A.length scan_idx /\
      SZ.fits (SZ.v n * SZ.v n)
    )
  ensures exists* scolor' sd' sf' spred' sstack' sscan' (cf: nat).
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to f sf' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    GR.pts_to ctr cf **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sd' == SZ.v n /\
      Seq.length sf' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\
      Seq.length sscan' == SZ.v n /\
      // All vertices eventually colored BLACK (finished)
      (forall (u: nat). u < SZ.v n ==> Seq.index scolor' u == 2) /\
      // Discovery and finish times are positive
      (forall (u: nat). u < SZ.v n ==> Seq.index sd' u > 0) /\
      (forall (u: nat). u < SZ.v n ==> Seq.index sf' u > 0) /\
      // Discovery time < finish time (parenthesis theorem)
      (forall (u: nat). u < SZ.v n ==> Seq.index sd' u < Seq.index sf' u) /\
      // Complexity: at most 2 * n² ticks
      cf >= reveal c0 /\
      cf - reveal c0 <= 2 * (SZ.v n * SZ.v n)
    )
{
  // Step 1: Initialize all vertices
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi scolor_i sd_i sf_i spred_i (vc: nat).
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to color scolor_i **
    A.pts_to d sd_i **
    A.pts_to f sf_i **
    A.pts_to pred spred_i **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length scolor_i == SZ.v n /\
      Seq.length sd_i == SZ.v n /\
      Seq.length sf_i == SZ.v n /\
      Seq.length spred_i == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index scolor_i j == 0) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index sd_i j == (-1)) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index sf_i j == (-1)) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index spred_i j == (-1)) /\
      vc == reveal c0
    )
  {
    let vi = !i;
    A.op_Array_Assignment color vi 0;      // WHITE
    A.op_Array_Assignment d vi (-1);
    A.op_Array_Assignment f vi (-1);
    A.op_Array_Assignment pred vi (-1);
    i := SZ.add vi 1sz
  };

  // Step 1b: Initialize scan_idx array
  i := 0sz;
  while (!i <^ n)
  invariant exists* vi scolor_ib sd_ib sf_ib spred_ib sscan_ib (vc: nat).
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to color scolor_ib **
    A.pts_to d sd_ib **
    A.pts_to f sf_ib **
    A.pts_to pred spred_ib **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan_ib **
    GR.pts_to ctr vc **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length scolor_ib == SZ.v n /\
      Seq.length sd_ib == SZ.v n /\
      Seq.length sf_ib == SZ.v n /\
      Seq.length spred_ib == SZ.v n /\
      Seq.length sscan_ib == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> SZ.v (Seq.index sscan_ib j) == 0) /\
      (forall (j: nat). j < SZ.v n ==> Seq.index scolor_ib j == 0) /\
      (forall (j: nat). j < SZ.v n ==> Seq.index sd_ib j == (-1)) /\
      (forall (j: nat). j < SZ.v n ==> Seq.index sf_ib j == (-1)) /\
      (forall (j: nat). j < SZ.v n ==> Seq.index spred_ib j == (-1)) /\
      vc == reveal c0
    )
  {
    let vi = !i;
    A.op_Array_Assignment scan_idx vi 0sz;
    i := SZ.add vi 1sz
  };

  // Step 2: Initialize time and stack
  let mut time_ref: int = 0;
  let mut stack_top: SZ.t = 0sz;

  // Establish count_ones == 0 (all vertices are WHITE) and sum_scan_idx == 0
  with scolor_init. assert (A.pts_to color scolor_init);
  with sscan_init. assert (A.pts_to scan_idx sscan_init);
  S.count_ones_all_zero scolor_init (SZ.v n);
  sum_scan_idx_all_zero sscan_init (SZ.v n);

  // Step 3: Main DFS loop - for each vertex s
  let mut s: SZ.t = 0sz;
  while (!s <^ n)
  invariant exists* vs vtop vtime scolor_s sd_s sf_s spred_s sstack_s sscan_s (vc_s: nat).
    R.pts_to s vs **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    A.pts_to adj sadj **
    A.pts_to color scolor_s **
    A.pts_to d sd_s **
    A.pts_to f sf_s **
    A.pts_to pred spred_s **
    A.pts_to stack_data sstack_s **
    A.pts_to scan_idx sscan_s **
    GR.pts_to ctr vc_s **
    pure (
      SZ.v vs <= SZ.v n /\ SZ.v vtop == 0 /\
      Seq.length scolor_s == SZ.v n /\ Seq.length sd_s == SZ.v n /\
      Seq.length sf_s == SZ.v n /\ Seq.length spred_s == SZ.v n /\
      Seq.length sstack_s == SZ.v n /\ Seq.length sscan_s == SZ.v n /\
      vtime >= 0 /\ SZ.fits (SZ.v n * SZ.v n) /\
      S.stack_ok scolor_s sstack_s (SZ.v n) (SZ.v vtop) /\
      S.scan_ok sscan_s (SZ.v n) /\
      S.dfs_ok scolor_s sd_s sf_s (SZ.v n) /\
      S.nonwhite_below scolor_s (SZ.v vs) /\
      (* Complexity: vc_s == c0 + vs + sum_scan_idx *)
      vc_s == reveal c0 + SZ.v vs + sum_scan_idx sscan_s (SZ.v n) /\
      (* WHITE vertices have scan_idx == 0 *)
      (forall (j:nat). j < SZ.v n ==> (Seq.index scolor_s j == 0 ==> SZ.v (Seq.index sscan_s j) == 0))
    )
  {
    let vs = !s;

    // Tick for outer loop iteration (checking color)
    tick ctr;

    // Check if s is WHITE
    let cs: int = A.op_Array_Access color vs;
    
    // Conditionally perform DFS-VISIT
    maybe_dfs_visit adj n vs cs color d f pred stack_data scan_idx stack_top time_ref ctr;

    s := SZ.add vs 1sz
  };
  
  // Prove final postcondition
  with scolor_final. assert (A.pts_to color scolor_final);
  with sd_final. assert (A.pts_to d sd_final);
  with sf_final. assert (A.pts_to f sf_final);
  with sscan_final. assert (A.pts_to scan_idx sscan_final);
  with sstack_final. assert (A.pts_to stack_data sstack_final);
  with vc_final. assert (GR.pts_to ctr vc_final);
  
  // From loop invariant: vc_final == c0 + n + sum_scan_idx sscan_final n
  // and sum_scan_idx sscan_final n <= n * n (since each scan_idx <= n, by scan_ok)
  sum_scan_idx_bound sscan_final (SZ.v n) (SZ.v n);
  // So vc_final - c0 = n + sum_scan_idx <= n + n*n
  // And n + n*n <= 2*n*n (since n >= 1)
  lemma_dfs_bound_correct (SZ.v n) (SZ.v n * SZ.v n) (SZ.v n);
  
  // Assert complexity bound
  assert (pure (vc_final >= reveal c0));
  assert (pure (vc_final - reveal c0 <= 2 * (SZ.v n * SZ.v n)));
  
  // Extract facts from loop invariant for final_postcondition_lemma
  // stack_ok with top==0 gives count_ones == 0
  assert (pure (S.count_ones scolor_final (SZ.v n) == 0));
  assert (pure (S.nonwhite_below scolor_final (SZ.v n)));
  assert (pure (S.dfs_ok scolor_final sd_final sf_final (SZ.v n)));
  S.final_postcondition_lemma scolor_final sd_final sf_final (SZ.v n);
  // Assert each postcondition quantifier explicitly
  assert (pure (forall (u: nat). u < SZ.v n ==> Seq.index scolor_final u == 2));
  assert (pure (forall (u: nat). u < SZ.v n ==> Seq.index sd_final u > 0));
  assert (pure (forall (u: nat). u < SZ.v n ==> Seq.index sf_final u > 0));
  assert (pure (forall (u: nat). u < SZ.v n ==> Seq.index sd_final u < Seq.index sf_final u))
}
#pop-options
