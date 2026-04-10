(*
   Heapsort Bridge Lemmas — proofs.

   NO admits. NO assumes.
*)
module CLRS.Ch06.Heap.C.BridgeLemmas

open CLRS.Ch06.Heap.Spec
open CLRS.Ch06.Heap.Lemmas
module Seq  = FStar.Seq
module I32  = FStar.Int32
module SZ   = FStar.SizeT
module Classical = FStar.Classical

// ================================================================
// extract_ints
// ================================================================

let extract_ints (s: Seq.seq (option I32.t)) (n: nat{all_some s n})
  : Tot (r: Seq.seq int{Seq.length r == n /\
    (forall (i: nat). i < n ==> Seq.index r i == I32.v (Some?.v (Seq.index s i)))})
  = Seq.init n (fun (i: nat{i < n}) -> (I32.v (Some?.v (Seq.index s i)) <: int))

// ================================================================
// root_ge_element_bridge
// ================================================================

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"

let root_ge_element_bridge (va: Seq.seq (option I32.t)) (n: SZ.t) =
  let nv = SZ.v n in
  // all_some va nv follows from array_initialized + nv <= Seq.length va
  let ints = extract_ints va nv in
  // Show heap_down_at ints nv k for each k < nv.
  // Convert from SizeT.t quantifier to nat by constructing SizeT.uint_to_t k.
  let aux_heap (k: nat{k < nv})
    : Lemma (heap_down_at ints nv k)
    = let _ : SZ.t = SZ.uint_to_t k in
      ()
  in
  Classical.forall_intro (Classical.move_requires aux_heap);
  assert (is_max_heap ints nv);
  // Root dominance via inductive lemma
  let aux_root (i: nat{i < nv})
    : Lemma (Seq.index ints 0 >= Seq.index ints i)
    = root_ge_element ints nv i
  in
  Classical.forall_intro (Classical.move_requires aux_root)

#pop-options
