module TestWithoutLemma
open CLRS.Ch32.RabinKarp.Spec

// Test that we can use the functions
let test () = 
  let text = Seq.seq_of_list [1;2;3;4] in
  let pattern = Seq.seq_of_list [2;3] in
  rabin_karp_find_all text pattern 10 13
