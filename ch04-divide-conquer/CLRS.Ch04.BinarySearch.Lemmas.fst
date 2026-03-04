(*
   Binary Search — Lemmas about the pure specification

   Proves monotonicity and halving properties of log2f,
   used by the binary search complexity proof.

   NO admits. NO assumes.
*)

module CLRS.Ch04.BinarySearch.Lemmas
open CLRS.Ch04.BinarySearch.Spec

// log2f is monotone: a <= b ==> log2f a <= log2f b
let rec lemma_log2f_mono (a b: int)
  : Lemma (requires a >= 1 /\ b >= 1 /\ a <= b)
          (ensures log2f a <= log2f b)
          (decreases (if a > 0 then a else 0))
  = if Prims.op_LessThanOrEqual a 1 then ()
    else if Prims.op_LessThanOrEqual b 1 then ()
    else (
      FStar.Math.Lemmas.lemma_div_le a b 2;
      lemma_log2f_mono (Prims.op_Division a 2) (Prims.op_Division b 2)
    )

// Halving reduces log2f by at least 1
let lemma_log2f_step (old_range new_range: int)
  : Lemma (requires old_range >= 1 /\ new_range >= 0 /\ new_range <= old_range / 2)
          (ensures (new_range >= 1 ==> log2f new_range + 1 <= log2f old_range) /\
                   (new_range == 0 ==> 1 <= log2f old_range + 1))
  = if new_range >= 1 then
      lemma_log2f_mono new_range (Prims.op_Division old_range 2)
    else ()
