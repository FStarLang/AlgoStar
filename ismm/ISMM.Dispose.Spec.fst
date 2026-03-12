(*
   ISMM Dispose — Pure Specification
   
   Specifies the dispose algorithm from paper §3.4, Fig. 4.
   Three-stack algorithm: dfs, scc, free_list.
   
   The dispose algorithm processes an SCC whose RC hit 0:
   1. DFS stack walks the DAG of SCCs
   2. SCC stack collects all nodes in the current SCC (via REP pointers)
   3. Free list accumulates nodes to deallocate
   For each node in the SCC, we examine its fields:
   - If field points to PROCESSING node in same SCC: add to scc stack
   - If field points to RC node in different SCC: decref; if RC=0, push to dfs
*)
module ISMM.Dispose.Spec

open FStar.Seq
module Spec = ISMM.UnionFind.Spec
open ISMM.Status

(** A node is "processing" if its tag is tag_rep (2) — reused during dispose *)
let is_processing (tag: seq int) (i: nat) : bool =
  i < Seq.length tag && Seq.index tag i = tag_rep

(** All nodes in an SCC (nodes whose find == rep).
    Requires uf_inv for pure_find. *)
let in_scc (st: Spec.uf_state{Spec.uf_inv st}) (rep: nat) (i: nat) : bool =
  i < st.n && Spec.pure_find st i = rep

(** After dispose, all nodes in the disposed SCC should be deallocated.
    We model this by setting their tag to a special "freed" value.
    For simplicity, we reuse tag_unmarked (0) as "freed". *)

(** dispose_post: postcondition for dispose(r)
    - All nodes in the SCC of r are freed (tag set to 0)
    - For each child SCC reachable from the disposed SCC:
      - If the child's RC was > 1: RC decremented by the number of edges from disposed SCC
      - If the child's RC reached 0: recursively disposed *)
let dispose_frees_scc (tag_before tag_after: seq int) (st: Spec.uf_state{Spec.uf_inv st}) (rep: nat) : prop =
  st.n <= Seq.length tag_after /\
  st.n <= Seq.length tag_before /\
  (forall (i: nat). i < st.n ==>
    (Spec.pure_find st i = rep ==> Seq.index tag_after i = tag_unmarked))

let dispose_preserves_others (tag_before tag_after: seq int) (st: Spec.uf_state{Spec.uf_inv st}) (rep: nat) : prop =
  st.n <= Seq.length tag_after /\
  st.n <= Seq.length tag_before /\
  (forall (i: nat). i < st.n ==>
    (Spec.pure_find st i <> rep ==>
      (Seq.index tag_after i = tag_unmarked \/ Seq.index tag_after i = Seq.index tag_before i)))

(** The dispose algorithm terminates because:
    - Each SCC is visited at most once on the dfs stack
    - The SCC DAG is acyclic (guaranteed by freeze)
    - Each node is pushed to scc/free_list at most once *)

(** Combined dispose postcondition *)
let dispose_post (tag_before tag_after: seq int) (st: Spec.uf_state{Spec.uf_inv st}) (rep: nat) : prop =
  dispose_frees_scc tag_before tag_after st rep /\
  dispose_preserves_others tag_before tag_after st rep /\
  Seq.length tag_after = Seq.length tag_before
