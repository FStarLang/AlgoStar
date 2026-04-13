(*
   Heapsort Bridge Lemmas — proofs.

   NO admits. NO assumes.
*)
module CLRS.Ch06.Heap.C.BridgeLemmas

open CLRS.Ch06.Heap.Spec
open CLRS.Ch06.Heap.Lemmas
module Seq  = FStar.Seq
module SeqP = FStar.Seq.Properties
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
// Permutation lemmas for option Int32.t sequences
// ================================================================

let option_perm_refl (s: Seq.seq (option I32.t))
  : Lemma (SeqP.permutation (option I32.t) s s)
  = ()

let option_perm_trans (s1 s2 s3: Seq.seq (option I32.t))
  : Lemma
    (requires SeqP.permutation (option I32.t) s1 s2 /\
              SeqP.permutation (option I32.t) s2 s3)
    (ensures SeqP.permutation (option I32.t) s1 s3)
  = ()

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

let swap_option_seq_eq (s: Seq.seq (option I32.t))
  (i j: nat{i < Seq.length s /\ j < Seq.length s /\ i <> j})
  : Lemma
    (Seq.equal
      (Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i))
      (SeqP.swap s i j))
  = ()

#pop-options

private let rec count_ext (#a: eqtype) (x: a) (s1 s2: Seq.seq a)
  : Lemma
    (requires Seq.equal s1 s2)
    (ensures SeqP.count x s1 = SeqP.count x s2)
    (decreases Seq.length s1)
  = if Seq.length s1 = 0 then ()
    else count_ext x (Seq.tail s1) (Seq.tail s2)

private let perm_ext (#a: eqtype) (s1 s2 s3: Seq.seq a)
  : Lemma
    (requires SeqP.permutation a s1 s2 /\ Seq.equal s2 s3)
    (ensures SeqP.permutation a s1 s3)
  = let aux (x: a) : Lemma (SeqP.count x s1 = SeqP.count x s3) =
      count_ext x s2 s3
    in
    Classical.forall_intro aux

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

let swap_option_perm (s: Seq.seq (option I32.t))
  (i j: nat{i < Seq.length s /\ j < Seq.length s})
  : Lemma (SeqP.permutation (option I32.t) s
    (Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i)))
  = if i = j then begin
      assert (Seq.equal s (Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i)));
      perm_ext s s (Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i))
    end
    else begin
      let lo = if i <= j then i else j in
      let hi = if i <= j then j else i in
      SeqP.lemma_swap_permutes #(option I32.t) s lo hi;
      assert (Seq.equal (SeqP.swap s lo hi) (SeqP.swap s i j));
      perm_ext s (SeqP.swap s lo hi) (SeqP.swap s i j);
      swap_option_seq_eq s i j;
      perm_ext s (SeqP.swap s i j) (Seq.upd (Seq.upd s i (Seq.index s j)) j (Seq.index s i))
    end

#pop-options

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
