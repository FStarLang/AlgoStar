(*
   ISMM RefCount — Pure Specification
   
   Specifies acquire/release from paper §3.2.
   - acquire(r): find(r), then incref representative
   - release(r): find(r), then decref; if RC=0, dispose
*)
module ISMM.RefCount.Spec

open FStar.Seq
module Spec = ISMM.UnionFind.Spec
open ISMM.Status

(** acquire_post: after acquire(r), the RC of find(r) is incremented by 1 *)
let acquire_post (rank_before rank_after: seq int) (st: Spec.uf_state{Spec.uf_inv st}) (r: nat{r < st.n}) : prop =
  Spec.pure_find_is_root st r;
  let rep = Spec.pure_find st r in
  st.n <= Seq.length rank_before /\
  st.n <= Seq.length rank_after /\
  Seq.length rank_after = Seq.length rank_before /\
  Seq.index rank_after rep = Seq.index rank_before rep + 1 /\
  (forall (i: nat). (i < st.n /\ i <> rep) ==> Seq.index rank_after i = Seq.index rank_before i)

(** release_post: after release(r), the RC of find(r) is decremented by 1.
    If RC reaches 0, dispose is triggered (modeled separately). *)
let release_post (rank_before rank_after: seq int) (st: Spec.uf_state{Spec.uf_inv st}) (r: nat{r < st.n}) : prop =
  Spec.pure_find_is_root st r;
  let rep = Spec.pure_find st r in
  st.n <= Seq.length rank_before /\
  st.n <= Seq.length rank_after /\
  Seq.length rank_after = Seq.length rank_before /\
  Seq.index rank_after rep = Seq.index rank_before rep - 1
