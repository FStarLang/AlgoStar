(*
   Binary Search — Lemmas interface
*)

module CLRS.Ch04.BinarySearch.Lemmas
open CLRS.Ch04.BinarySearch.Spec

val lemma_log2f_mono (a b: int)
  : Lemma (requires a >= 1 /\ b >= 1 /\ a <= b)
          (ensures log2f a <= log2f b)

val lemma_log2f_step (old_range new_range: int)
  : Lemma (requires old_range >= 1 /\ new_range >= 0 /\ new_range <= old_range / 2)
          (ensures (new_range >= 1 ==> log2f new_range + 1 <= log2f old_range) /\
                   (new_range == 0 ==> 1 <= log2f old_range + 1))
