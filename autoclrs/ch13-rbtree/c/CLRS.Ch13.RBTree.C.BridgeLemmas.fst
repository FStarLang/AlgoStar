(**
 * Proofs for the bridge lemmas connecting array-based C RB tree
 * operations to CLRS.Ch13.RBTree.Spec.
 *)
module CLRS.Ch13.RBTree.C.BridgeLemmas

open FStar.Mul
module S = CLRS.Ch13.RBTree.Spec
module L = CLRS.Ch13.RBTree.Lemmas

/// search_correct: by definitional unfolding of tree_of_cap and S.search
let search_correct nodes cap idx fuel k = ()
