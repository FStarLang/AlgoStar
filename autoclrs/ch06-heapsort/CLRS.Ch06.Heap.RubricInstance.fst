module CLRS.Ch06.Heap.RubricInstance
#lang-pulse

module HC = CLRS.Ch06.Heap.Complexity
module HR = CLRS.Ch06.Heap.Rubric
module SC = CLRS.Common.Complexity.Sorting.Class

instance heapsort_array_sort : SC.array_sort
  (fun n ->
    if n > 0 then
      (n / 2) * (2 * HC.log2_floor n) +
      (n - 1) * (2 * HC.log2_floor n)
    else 0)
= {
  sort = HR.heapsort_sort;
}
