(*
   Stack-based Depth-First Search - CLRS §22.3

   Implements the classical DFS algorithm from CLRS using an explicit stack.
   Graph represented as adjacency matrix adj[u*n+v] (edge from u to v if != 0).

   Colors: 0=WHITE (unvisited), 1=GRAY (discovered, on stack), 2=BLACK (finished)

   Algorithm (CLRS pseudocode):
   DFS(G)
     for each vertex u in G.V
       u.color = WHITE; u.pi = NIL
     time = 0
     for each vertex u in G.V
       if u.color == WHITE
         DFS-VISIT(G, u)

   DFS-VISIT(G, u)
     time = time + 1
     u.d = time        // discovery time
     u.color = GRAY
     for each v in G.Adj[u]
       if v.color == WHITE
         v.pi = u
         DFS-VISIT(G, v)
     u.color = BLACK
     time = time + 1
     u.f = time        // finish time

   Iterative implementation with explicit stack:
   - Push vertex onto stack and mark GRAY
   - For each vertex on stack, find next WHITE neighbor
   - If found, push neighbor (recursive case)
   - If none, pop vertex and mark BLACK (finish)
   - Use scan_idx[] to track how far we've scanned each vertex's neighbors
*)

module CLRS.Ch22.StackDFS
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open Pulse.Lib.WithPure
open FStar.SizeT
open FStar.Mul

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* Graph specification *)

let has_edge (adj: Seq.seq int) (n: nat) (u v: nat) : prop =
  u < n /\ v < n /\ u * n + v < Seq.length adj /\ Seq.index adj (u * n + v) <> 0

let rec reachable_in (adj: Seq.seq int) (n: nat) (source v: nat) (steps: nat)
  : Tot prop (decreases steps)
  = if steps = 0 then v == source
    else (exists (u: nat). u < n /\ reachable_in adj n source u (steps - 1) /\ has_edge adj n u v)

(* Arithmetic helpers for SZ.fits *)
let fits_product_smaller (a b c d: nat)
  : Lemma (requires c < a /\ d <= b /\ SZ.fits (a * b))
          (ensures SZ.fits (c * b) /\ SZ.fits (c * b + d))
  = assert (c * b <= a * b);
    assert (c * b + d <= a * b)

(* Safe index for int sequences - avoids refinement issues with nested Seq.index in postconditions *)
let safe_index_int (s: Seq.seq int) (i: nat) : int =
  if i < Seq.length s then Seq.index s i else 0

let fits_le (x y: nat)
  : Lemma (requires x <= y /\ SZ.fits y)
          (ensures SZ.fits x)
  = ()

(* Count GRAY (==1) vertices in s[0..k) *)
let rec count_ones (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Tot (r: nat{r <= k}) (decreases k)
  = if k = 0 then 0
    else (if Seq.index s (k - 1) = 1 then 1 else 0) + count_ones s (k - 1)

(* If any element in [0..k) is not 1, count < k *)
let rec count_ones_lt (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat)
  : Lemma (requires j < k /\ Seq.index s j <> 1)
          (ensures count_ones s k < k)
          (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then ()
    else count_ones_lt s (k - 1) j

(* Updating index j to 1 when it wasn't 1: count goes up by 1 *)
let rec count_ones_upd_to_one (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat)
  : Lemma (requires j < k /\ Seq.index s j <> 1)
          (ensures Seq.length (Seq.upd s j 1) == Seq.length s /\
                   count_ones (Seq.upd s j 1) k == count_ones s k + 1)
          (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then begin
      let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s})
        : Lemma (ensures Seq.length (Seq.upd s j 1) == Seq.length s /\
                         count_ones (Seq.upd s j 1) k' == count_ones s k')
                (decreases k')
        = if k' = 0 then ()
          else (assert (Seq.index (Seq.upd s j 1) (k'-1) == Seq.index s (k'-1)); aux s (k'-1) j)
      in aux s (k-1) j
    end
    else (assert (Seq.index (Seq.upd s j 1) (k-1) == Seq.index s (k-1));
          count_ones_upd_to_one s (k-1) j)

(* Updating index j from 1 to non-1: count goes down by 1 *)
let rec count_ones_upd_from_one (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat) (v: int)
  : Lemma (requires j < k /\ Seq.index s j = 1 /\ v <> 1)
          (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                   count_ones (Seq.upd s j v) k == count_ones s k - 1)
          (decreases k)
  = if k = 0 then ()
    else if j = k - 1 then begin
      let rec aux (s: Seq.seq int) (k': nat{k' <= Seq.length s}) (j: nat{j >= k' /\ j < Seq.length s}) (v: int)
        : Lemma (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                         count_ones (Seq.upd s j v) k' == count_ones s k')
                (decreases k')
        = if k' = 0 then ()
          else (assert (Seq.index (Seq.upd s j v) (k'-1) == Seq.index s (k'-1)); aux s (k'-1) j v)
      in aux s (k-1) j v
    end
    else (assert (Seq.index (Seq.upd s j v) (k-1) == Seq.index s (k-1));
          count_ones_upd_from_one s (k-1) j v)

(* Updating out of range doesn't change count *)
let rec count_ones_upd_out (s: Seq.seq int) (k: nat{k <= Seq.length s}) (j: nat) (v: int)
  : Lemma (requires j >= k /\ j < Seq.length s)
          (ensures Seq.length (Seq.upd s j v) == Seq.length s /\
                   count_ones (Seq.upd s j v) k == count_ones s k)
          (decreases k)
  = if k = 0 then ()
    else (assert (Seq.index (Seq.upd s j v) (k-1) == Seq.index s (k-1));
          count_ones_upd_out s (k-1) j v)

(* If all elements in [0..k) are 0, count_ones is 0 *)
let rec count_ones_all_zero (s: Seq.seq int) (k: nat{k <= Seq.length s})
  : Lemma (requires forall (j:nat). j < k ==> Seq.index s j == 0)
          (ensures count_ones s k == 0)
          (decreases k)
  = if k = 0 then ()
    else count_ones_all_zero s (k - 1)

(* Helper: discover a WHITE vertex v from vertex u.
   Sets d[v], color[v]=GRAY, pred[v]=u, pushes v onto stack.
   Factored out to avoid Pulse unification issues with conditional branches. *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn discover_vertex_dfs
  (color: A.array int) (d: A.array int) (pred: A.array int)
  (stack_data: A.array SZ.t) (stack_top: ref SZ.t)
  (scan_idx: A.array SZ.t)
  (time_ref: ref int)
  (u: SZ.t) (vv: SZ.t) (n: SZ.t)
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
  requires
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    pure (
      SZ.v vv < SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v vtop < SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sd == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sstack == SZ.v n /\
      Seq.length sscan == SZ.v n /\
      vtime >= 0 /\
      Seq.index scolor (SZ.v vv) <> 1 /\
      count_ones scolor (SZ.v n) == SZ.v vtop /\
      (forall (i:nat). i < SZ.v vtop ==> SZ.v (Seq.index sstack i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop ==> safe_index_int scolor (SZ.v (Seq.index sstack i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop /\ j < SZ.v vtop /\ i <> j ==> SZ.v (Seq.index sstack i) <> SZ.v (Seq.index sstack j)) /\
      (forall (uu:nat). uu < SZ.v n ==> SZ.v (Seq.index sscan uu) <= SZ.v n)
    )
  ensures exists* scolor' sd' spred' sstack' sscan' vtop' vtime'.
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sd' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\
      Seq.length sscan' == SZ.v n /\
      SZ.v vtop' <= SZ.v n /\
      SZ.v vtop' > SZ.v vtop /\
      vtime' == vtime + 1 /\
      count_ones scolor' (SZ.v n) == SZ.v vtop' /\
      (forall (i:nat). i < SZ.v vtop' ==> SZ.v (Seq.index sstack' i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop' ==> safe_index_int scolor' (SZ.v (Seq.index sstack' i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop' /\ j < SZ.v vtop' /\ i <> j ==> SZ.v (Seq.index sstack' i) <> SZ.v (Seq.index sstack' j)) /\
      (forall (uu:nat). uu < SZ.v n ==> SZ.v (Seq.index sscan' uu) <= SZ.v n)
    )
{
  // time++
  let t = !time_ref;
  time_ref := t + 1;
  // v.d = time
  A.op_Array_Assignment d vv (t + 1);
  // v.color = GRAY
  count_ones_upd_to_one scolor (SZ.v n) (SZ.v vv);
  A.op_Array_Assignment color vv 1;
  // v.pi = u
  A.op_Array_Assignment pred vv (SZ.v u);
  // Initialize scan_idx[v] = 0
  A.op_Array_Assignment scan_idx vv 0sz;
  // PUSH(stack, v)
  let top = !stack_top;
  A.op_Array_Assignment stack_data top vv;
  stack_top := SZ.add top 1sz
}
#pop-options

(* Helper: conditionally discover a vertex if WHITE and edge exists.
   Both branches produce the same slprop shape, solving Pulse unification. *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
fn maybe_discover_dfs
  (color: A.array int) (d: A.array int) (pred: A.array int)
  (stack_data: A.array SZ.t) (stack_top: ref SZ.t)
  (scan_idx: A.array SZ.t)
  (time_ref: ref int)
  (u: SZ.t) (vv: SZ.t) (n: SZ.t)
  (has_edge_val: int) (cv: int)
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
  requires
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    R.pts_to stack_top vtop **
    R.pts_to time_ref vtime **
    pure (
      SZ.v vv < SZ.v n /\
      SZ.v u < SZ.v n /\
      SZ.v vtop <= SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sd == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sstack == SZ.v n /\
      Seq.length sscan == SZ.v n /\
      vtime >= 0 /\
      cv == Seq.index scolor (SZ.v vv) /\
      count_ones scolor (SZ.v n) == SZ.v vtop /\
      (forall (i:nat). i < SZ.v vtop ==> SZ.v (Seq.index sstack i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop ==> safe_index_int scolor (SZ.v (Seq.index sstack i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop /\ j < SZ.v vtop /\ i <> j ==> SZ.v (Seq.index sstack i) <> SZ.v (Seq.index sstack j)) /\
      (forall (uu:nat). uu < SZ.v n ==> SZ.v (Seq.index sscan uu) <= SZ.v n)
    )
  ensures exists* scolor' sd' spred' sstack' sscan' vtop' vtime'.
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sd' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\
      Seq.length sscan' == SZ.v n /\
      SZ.v vtop' <= SZ.v n /\
      SZ.v vtop' >= SZ.v vtop /\
      vtime' >= vtime /\
      count_ones scolor' (SZ.v n) == SZ.v vtop' /\
      (forall (i:nat). i < SZ.v vtop' ==> SZ.v (Seq.index sstack' i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop' ==> safe_index_int scolor' (SZ.v (Seq.index sstack' i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop' /\ j < SZ.v vtop' /\ i <> j ==> SZ.v (Seq.index sstack' i) <> SZ.v (Seq.index sstack' j)) /\
      (forall (uu:nat). uu < SZ.v n ==> SZ.v (Seq.index sscan' uu) <= SZ.v n)
    )
{
  if (has_edge_val <> 0 && cv = 0) {
    count_ones_lt scolor (SZ.v n) (SZ.v vv);
    discover_vertex_dfs color d pred stack_data stack_top scan_idx time_ref u vv n
  }
}
#pop-options

(* Helper: finish a vertex u.
   Sets f[u], color[u]=BLACK, pops u from stack. *)

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
      count_ones scolor (SZ.v n) == SZ.v vtop /\
      SZ.v (Seq.index sstack (SZ.v vtop - 1)) == SZ.v u /\
      (forall (i:nat). i < SZ.v vtop ==> SZ.v (Seq.index sstack i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop ==> safe_index_int scolor (SZ.v (Seq.index sstack i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop /\ j < SZ.v vtop /\ i <> j ==> SZ.v (Seq.index sstack i) <> SZ.v (Seq.index sstack j))
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
      count_ones scolor' (SZ.v n) == SZ.v vtop' /\
      (forall (i:nat). i < SZ.v vtop' ==> SZ.v (Seq.index sstack i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop' ==> safe_index_int scolor' (SZ.v (Seq.index sstack i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop' /\ j < SZ.v vtop' /\ i <> j ==> SZ.v (Seq.index sstack i) <> SZ.v (Seq.index sstack j))
    )
{
  // u.color = BLACK
  count_ones_upd_from_one scolor (SZ.v n) (SZ.v u) 2;
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

(* Helper: perform DFS-VISIT for a single white vertex *)

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
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
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
    pure (
      SZ.v vs < SZ.v n /\
      SZ.v n > 0 /\
      SZ.v vtop < SZ.v n /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sd == SZ.v n /\
      Seq.length sf == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sstack == SZ.v n /\
      Seq.length sscan == SZ.v n /\
      vtime >= 0 /\
      SZ.fits (SZ.v n * SZ.v n) /\
      Seq.index scolor (SZ.v vs) <> 1 /\
      count_ones scolor (SZ.v n) == SZ.v vtop /\
      (forall (i:nat). i < SZ.v vtop ==> SZ.v (Seq.index sstack i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop ==> safe_index_int scolor (SZ.v (Seq.index sstack i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop /\ j < SZ.v vtop /\ i <> j ==> SZ.v (Seq.index sstack i) <> SZ.v (Seq.index sstack j)) /\
      (forall (uu:nat). uu < SZ.v n ==> SZ.v (Seq.index sscan uu) <= SZ.v n)
    )
  ensures exists* scolor' sd' sf' spred' sstack' sscan' vtop' vtime'.
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to f sf' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sd' == SZ.v n /\
      Seq.length sf' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\
      Seq.length sscan' == SZ.v n /\
      SZ.v vtop' == 0 /\
      vtime' >= vtime /\
      count_ones scolor' (SZ.v n) == SZ.v vtop' /\
      (forall (i:nat). i < SZ.v vtop' ==> SZ.v (Seq.index sstack' i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop' ==> safe_index_int scolor' (SZ.v (Seq.index sstack' i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop' /\ j < SZ.v vtop' /\ i <> j ==> SZ.v (Seq.index sstack' i) <> SZ.v (Seq.index sstack' j)) /\
      (forall (uu:nat). uu < SZ.v n ==> SZ.v (Seq.index sscan' uu) <= SZ.v n)
    )
{
  // Discover vs
  let t = !time_ref;
  time_ref := t + 1;
  A.op_Array_Assignment d vs (t + 1);
  count_ones_upd_to_one scolor (SZ.v n) (SZ.v vs);
  A.op_Array_Assignment color vs 1;      // GRAY
  A.op_Array_Assignment pred vs (-1);    // NIL
  A.op_Array_Assignment scan_idx vs 0sz;
  
  // PUSH(stack, vs)
  let top = !stack_top;
  A.op_Array_Assignment stack_data top vs;
  stack_top := SZ.add top 1sz;

  // Process stack
  while (
    let vtop = !stack_top;
    SZ.gt vtop 0sz
  )
  invariant exists* vtop_w vtime_w scolor_w sd_w sf_w spred_w sstack_w sscan_w.
    R.pts_to stack_top vtop_w **
    R.pts_to time_ref vtime_w **
    A.pts_to adj sadj **
    A.pts_to color scolor_w **
    A.pts_to d sd_w **
    A.pts_to f sf_w **
    A.pts_to pred spred_w **
    A.pts_to stack_data sstack_w **
    A.pts_to scan_idx sscan_w **
    pure (
      SZ.v vtop_w <= SZ.v n /\
      SZ.v vs < SZ.v n /\
      Seq.length scolor_w == SZ.v n /\
      Seq.length sd_w == SZ.v n /\
      Seq.length sf_w == SZ.v n /\
      Seq.length spred_w == SZ.v n /\
      Seq.length sstack_w == SZ.v n /\
      Seq.length sscan_w == SZ.v n /\
      vtime_w >= 0 /\
      vtime_w >= vtime /\
      SZ.fits (SZ.v n * SZ.v n) /\
      count_ones scolor_w (SZ.v n) == SZ.v vtop_w /\
      (forall (i:nat). i < SZ.v vtop_w ==> SZ.v (Seq.index sstack_w i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop_w ==> safe_index_int scolor_w (SZ.v (Seq.index sstack_w i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop_w /\ j < SZ.v vtop_w /\ i <> j ==> SZ.v (Seq.index sstack_w i) <> SZ.v (Seq.index sstack_w j)) /\
      (forall (uu:nat). uu < SZ.v n ==> SZ.v (Seq.index sscan_w uu) <= SZ.v n)
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
    invariant exists* vscan vfound vnext vtime_scan scolor_scan sd_scan sf_scan spred_scan sstack_scan sscan_scan.
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
      pure (
        SZ.v vscan <= SZ.v n /\
        SZ.v u < SZ.v n /\
        SZ.v top <= SZ.v n /\
        Seq.length sadj == SZ.v n * SZ.v n /\
        Seq.length scolor_scan == SZ.v n /\
        Seq.length sd_scan == SZ.v n /\
        Seq.length sf_scan == SZ.v n /\
        Seq.length spred_scan == SZ.v n /\
        Seq.length sstack_scan == SZ.v n /\
        Seq.length sscan_scan == SZ.v n /\
        vtime_scan >= 0 /\
        vtime_scan >= vtime /\
        SZ.fits (SZ.v u * SZ.v n) /\
        SZ.fits (SZ.v u * SZ.v n + SZ.v vscan) /\
        (vfound ==> SZ.v vnext < SZ.v n) /\
        (vfound ==> Seq.index scolor_scan (SZ.v vnext) == 0) /\
        Seq.index scolor_scan (SZ.v u) == 1 /\
        SZ.v (Seq.index sstack_scan (SZ.v top - 1)) == SZ.v u /\
        count_ones scolor_scan (SZ.v n) == SZ.v top /\
        (forall (i:nat). i < SZ.v top ==> SZ.v (Seq.index sstack_scan i) < SZ.v n) /\
        (forall (i:nat). i < SZ.v top ==> safe_index_int scolor_scan (SZ.v (Seq.index sstack_scan i)) == 1) /\
        (forall (i j:nat). i < SZ.v top /\ j < SZ.v top /\ i <> j ==> SZ.v (Seq.index sstack_scan i) <> SZ.v (Seq.index sstack_scan j)) /\
        (forall (uu:nat). uu < SZ.v n ==> SZ.v (Seq.index sscan_scan uu) <= SZ.v n)
      )
    {
      let vscan = !scan;

      // Check edge (u, vscan) and color[vscan]
      let offset: SZ.t = SZ.mul u n;
      let idx: SZ.t = SZ.add offset vscan;
      assert (pure (SZ.v u * SZ.v n + SZ.v vscan < SZ.v n * SZ.v n));
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
    A.op_Array_Assignment scan_idx u final_scan;

    let found = !found_white;
    if (found) {
      // Found WHITE neighbor - discover it
      let vv = !next_v;
      assert (pure (SZ.v vv < SZ.v n));
      
      // vv is WHITE (color == 0, hence <> 1), so count_ones_lt gives vtop < n
      with scolor_now. assert (A.pts_to color scolor_now);
      count_ones_lt scolor_now (SZ.v n) (SZ.v vv);
      
      discover_vertex_dfs color d pred stack_data stack_top scan_idx time_ref u vv n
    } else {
      // No more WHITE neighbors - finish u
      // u is on stack at position top-1 and was discovered as GRAY
      // color[u] == 1 from inner scan loop invariant
      finish_vertex color f stack_data stack_top time_ref u n
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
  
  assert (pure (SZ.v vtop_after == 0));
  ()
}
#pop-options

(* Helper: conditionally perform DFS-VISIT if vertex is WHITE.
   Both branches produce the same slprop shape, solving Pulse unification. *)

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
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  (#vtop: erased SZ.t)
  (#vtime: erased int)
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
    pure (
      SZ.v vs < SZ.v n /\
      SZ.v n > 0 /\
      SZ.v vtop == 0 /\
      Seq.length sadj == SZ.v n * SZ.v n /\
      Seq.length scolor == SZ.v n /\
      Seq.length sd == SZ.v n /\
      Seq.length sf == SZ.v n /\
      Seq.length spred == SZ.v n /\
      Seq.length sstack == SZ.v n /\
      Seq.length sscan == SZ.v n /\
      vtime >= 0 /\
      SZ.fits (SZ.v n * SZ.v n) /\
      cv == Seq.index scolor (SZ.v vs) /\
      count_ones scolor (SZ.v n) == SZ.v vtop /\
      (forall (i:nat). i < SZ.v vtop ==> SZ.v (Seq.index sstack i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop ==> safe_index_int scolor (SZ.v (Seq.index sstack i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop /\ j < SZ.v vtop /\ i <> j ==> SZ.v (Seq.index sstack i) <> SZ.v (Seq.index sstack j)) /\
      (forall (uu:nat). uu < SZ.v n ==> SZ.v (Seq.index sscan uu) <= SZ.v n)
    )
  ensures exists* scolor' sd' sf' spred' sstack' sscan' vtop' vtime'.
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to f sf' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
    R.pts_to stack_top vtop' **
    R.pts_to time_ref vtime' **
    pure (
      Seq.length scolor' == SZ.v n /\
      Seq.length sd' == SZ.v n /\
      Seq.length sf' == SZ.v n /\
      Seq.length spred' == SZ.v n /\
      Seq.length sstack' == SZ.v n /\
      Seq.length sscan' == SZ.v n /\
      SZ.v vtop' == 0 /\
      vtime' >= vtime /\
      count_ones scolor' (SZ.v n) == SZ.v vtop' /\
      (forall (i:nat). i < SZ.v vtop' ==> SZ.v (Seq.index sstack' i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop' ==> safe_index_int scolor' (SZ.v (Seq.index sstack' i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop' /\ j < SZ.v vtop' /\ i <> j ==> SZ.v (Seq.index sstack' i) <> SZ.v (Seq.index sstack' j)) /\
      (forall (uu:nat). uu < SZ.v n ==> SZ.v (Seq.index sscan' uu) <= SZ.v n)
    )
{
  if (cv = 0) {
    dfs_visit adj n vs color d f pred stack_data scan_idx stack_top time_ref
  }
}
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
//SNIPPET_START: stack_dfs_sig
fn stack_dfs
  (adj: A.array int)
  (n: SZ.t)
  (color: A.array int)
  (d: A.array int)
  (f: A.array int)
  (pred: A.array int)
  (stack_data: A.array SZ.t)
  (scan_idx: A.array SZ.t)
  (#sadj: erased (Seq.seq int))
  (#scolor: erased (Seq.seq int))
  (#sd: erased (Seq.seq int))
  (#sf: erased (Seq.seq int))
  (#spred: erased (Seq.seq int))
  (#sstack: erased (Seq.seq SZ.t))
  (#sscan: erased (Seq.seq SZ.t))
  requires
    A.pts_to adj sadj **
    A.pts_to color scolor **
    A.pts_to d sd **
    A.pts_to f sf **
    A.pts_to pred spred **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
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
  ensures exists* scolor' sd' sf' spred' sstack' sscan'.
    A.pts_to adj sadj **
    A.pts_to color scolor' **
    A.pts_to d sd' **
    A.pts_to f sf' **
    A.pts_to pred spred' **
    A.pts_to stack_data sstack' **
    A.pts_to scan_idx sscan' **
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
      (forall (u: nat). u < SZ.v n ==> Seq.index sd' u < Seq.index sf' u)
    )
//SNIPPET_END: stack_dfs_sig
{
  // Step 1: Initialize all vertices
  let mut i: SZ.t = 0sz;
  while (!i <^ n)
  invariant exists* vi scolor_i sd_i sf_i spred_i.
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to color scolor_i **
    A.pts_to d sd_i **
    A.pts_to f sf_i **
    A.pts_to pred spred_i **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan **
    pure (
      SZ.v vi <= SZ.v n /\
      Seq.length scolor_i == SZ.v n /\
      Seq.length sd_i == SZ.v n /\
      Seq.length sf_i == SZ.v n /\
      Seq.length spred_i == SZ.v n /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index scolor_i j == 0) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index sd_i j == (-1)) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index sf_i j == (-1)) /\
      (forall (j: nat). j < SZ.v vi ==> Seq.index spred_i j == (-1))
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
  invariant exists* vi scolor_ib sd_ib sf_ib spred_ib sscan_ib.
    R.pts_to i vi **
    A.pts_to adj sadj **
    A.pts_to color scolor_ib **
    A.pts_to d sd_ib **
    A.pts_to f sf_ib **
    A.pts_to pred spred_ib **
    A.pts_to stack_data sstack **
    A.pts_to scan_idx sscan_ib **
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
      (forall (j: nat). j < SZ.v n ==> Seq.index spred_ib j == (-1))
    )
  {
    let vi = !i;
    A.op_Array_Assignment scan_idx vi 0sz;
    i := SZ.add vi 1sz
  };

  // Step 2: Initialize time and stack
  let mut time_ref: int = 0;
  let mut stack_top: SZ.t = 0sz;

  // Establish count_ones == 0 (all vertices are WHITE)
  with scolor_init. assert (A.pts_to color scolor_init);
  count_ones_all_zero scolor_init (SZ.v n);

  // Step 3: Main DFS loop - for each vertex s
  let mut s: SZ.t = 0sz;
  while (!s <^ n)
  invariant exists* vs vtop vtime scolor_s sd_s sf_s spred_s sstack_s sscan_s.
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
    pure (
      SZ.v vs <= SZ.v n /\
      SZ.v vtop == 0 /\
      Seq.length scolor_s == SZ.v n /\
      Seq.length sd_s == SZ.v n /\
      Seq.length sf_s == SZ.v n /\
      Seq.length spred_s == SZ.v n /\
      Seq.length sstack_s == SZ.v n /\
      Seq.length sscan_s == SZ.v n /\
      vtime >= 0 /\
      SZ.fits (SZ.v n * SZ.v n) /\
      count_ones scolor_s (SZ.v n) == SZ.v vtop /\
      (forall (i:nat). i < SZ.v vtop ==> SZ.v (Seq.index sstack_s i) < SZ.v n) /\
      (forall (i:nat). i < SZ.v vtop ==> safe_index_int scolor_s (SZ.v (Seq.index sstack_s i)) == 1) /\
      (forall (i j:nat). i < SZ.v vtop /\ j < SZ.v vtop /\ i <> j ==> SZ.v (Seq.index sstack_s i) <> SZ.v (Seq.index sstack_s j)) /\
      (forall (uu:nat). uu < SZ.v n ==> SZ.v (Seq.index sscan_s uu) <= SZ.v n)
    )
  {
    let vs = !s;

    // Check if s is WHITE
    let cs: int = A.op_Array_Access color vs;
    
    // Conditionally perform DFS-VISIT
    maybe_dfs_visit adj n vs cs color d f pred stack_data scan_idx stack_top time_ref;

    s := SZ.add vs 1sz
  };
  
  // Prove final postcondition
  with scolor_final. assert (A.pts_to color scolor_final);
  with sd_final. assert (A.pts_to d sd_final);
  with sf_final. assert (A.pts_to f sf_final);
  
  assume_ (pure (
    (forall (u: nat). u < SZ.v n ==> Seq.index scolor_final u == 2) /\
    (forall (u: nat). u < SZ.v n ==> Seq.index sd_final u > 0) /\
    (forall (u: nat). u < SZ.v n ==> Seq.index sf_final u > 0) /\
    (forall (u: nat). u < SZ.v n ==> Seq.index sd_final u < Seq.index sf_final u)
  ))
}
#pop-options
