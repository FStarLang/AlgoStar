module Tmp
open FStar.Seq
module Seq = FStar.Seq
let input  = Seq.seq_of_list [3; 1; 2]
let output = Seq.seq_of_list [1; 2; 3]// Spec: sorted ∧ permutation
let soundness_test () : Lemma(is_sorted output /\ is_permutation input output)= ()   // F* + Z3 discharge this automatically