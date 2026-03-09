(*
   Abstract sentinel constant for infinity.

   The concrete value is hidden behind this interface so that proofs
   cannot depend on a specific numeric choice. The only property
   exposed is inf > 0, which is the minimum needed by the
   shortest-path specification and algorithms.
*)

module CLRS.Ch24.ShortestPath.Inf

val inf : i:int{i > 0}
