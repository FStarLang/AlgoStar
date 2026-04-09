module MergeSortHelper

open FStar.Math.Lemmas

let mod_range (m w: nat) (k: nat)
  : Lemma
    (requires w >= 1 /\ m % w = 0 /\ m <= k /\ k + 1 < m + w)
    (ensures (k + 1) % w <> 0)
  = modulo_lemma (k + 1 - m) w;
    lemma_mod_plus (k + 1 - m) (m / w) w;
    lemma_div_exact m w
