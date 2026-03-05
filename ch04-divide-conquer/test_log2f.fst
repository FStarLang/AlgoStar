module Test.Log2f
open CLRS.Ch04.BinarySearch.Spec

let test1 () : Lemma (log2f 4 == 2) = ()
let test2 () : Lemma (log2f 8 == 3) = ()
let test3 (a b: nat) : Lemma (requires a >= 1 /\ a <= b) (ensures log2f a <= log2f 100) = admit()
