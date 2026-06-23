module CLRS.Ch06.Heap.RubricInstance
#lang-pulse

module CB = CLRS.Ch06.Heap.CostBound
module HR = CLRS.Ch06.Heap.Rubric
module SC = CLRS.Common.Complexity.Sorting.Class

instance heapsort_array_sort (a: eqtype) : SC.array_sort a CB.heapsort_cost_bound = {
  sort = HR.heapsort_sort #a;
}
