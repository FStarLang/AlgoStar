module CLRS.Ch06.Heap.RubricInstance
#lang-pulse

module HC = CLRS.Ch06.Heap.Complexity
module HR = CLRS.Ch06.Heap.Rubric
module SC = CLRS.Common.Complexity.Sorting.Class

instance heapsort_array_sort (a: eqtype) : SC.array_sort a
  (fun n ->
    if n = 0 then 0
    else (n / 2) * (2 * HC.log2_floor n) +
         (n - 1) * (2 * HC.log2_floor n))
= {
  sort = HR.heapsort_sort #a;
}
