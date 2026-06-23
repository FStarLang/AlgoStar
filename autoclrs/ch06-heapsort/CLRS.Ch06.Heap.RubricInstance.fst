module CLRS.Ch06.Heap.RubricInstance
#lang-pulse

module CB = CLRS.Ch06.Heap.CostBound
module C = Pulse.Lib.Core
module HR = CLRS.Ch06.Heap.Rubric
module SC = CLRS.Common.Complexity.Sorting.Class

let register_sep_laws () : Lemma True = C.slprop_equivs ()

instance heapsort_array_sort (a: eqtype) : SC.array_sort a CB.heapsort_cost_bound = {
  sort = (register_sep_laws (); HR.heapsort_sort #a);
}
