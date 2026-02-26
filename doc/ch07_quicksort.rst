.. _Ch07_Quicksort:

#############################
Quicksort
#############################

This chapter covers the quicksort algorithm from CLRS Chapter 7, including
the Lomuto partition scheme (§7.1), a two-pointer partition variant, and
the recursive quicksort algorithm. All modules are fully verified with
**zero admits, assumes, or assume\_ calls**. For each component we prove:

1. The output is a permutation of the input.
2. The partition predicate holds (elements ≤ pivot before split, > pivot after).
3. The final array is sorted.
4. Worst-case complexity is O(n²).

Partition
=========

CLRS §7.1 presents partition as the key subroutine of quicksort. We provide
two implementations: a standalone two-pointer partition and the faithful
Lomuto scheme.

Two-Pointer Partition
~~~~~~~~~~~~~~~~~~~~~

The ``is_partitioned`` predicate captures the partition postcondition — all
elements before the split point are ≤ the pivot, all from the split point
onward are > the pivot:

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.Partition.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_partitioned
   :end-before: //SNIPPET_END: is_partitioned

The Pulse implementation scans the array with two indices ``i`` and ``j``.
At each step it compares ``a[j]`` to the pivot and conditionally swaps
``a[i]`` and ``a[j]``, advancing ``i`` when a swap occurs. The function
also proves **exactly n comparisons** via a ghost tick counter. The
postcondition guarantees: (1) the result is a valid split point, (2)
the output is a permutation of the input, (3) the partition predicate
holds, and (4) the complexity bound:

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.Partition.fst
   :language: pulse
   :start-after: //SNIPPET_START: partition_sig
   :end-before: //SNIPPET_END: partition_sig

Lomuto Partition
~~~~~~~~~~~~~~~~

The Lomuto scheme is the CLRS textbook version: the pivot is the last
element ``A[r]``, and the algorithm partitions ``A[p..r]`` around it.
The key predicate tracks the pivot at position ``q`` after the final swap:

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.LomutoPartition.fst
   :language: fstar
   :start-after: //SNIPPET_START: is_lomuto_partitioned
   :end-before: //SNIPPET_END: is_lomuto_partitioned

The Lomuto ``lomuto_partition`` function signature:

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.LomutoPartition.fst
   :language: pulse
   :start-after: //SNIPPET_START: lomuto_partition_sig
   :end-before: //SNIPPET_END: lomuto_partition_sig

The loop invariant tracks three regions: elements ``A[p..i]`` are ≤ pivot,
elements ``A[i+1..j-1]`` are > pivot, and the pivot remains at ``A[r]``.
After the loop, a final swap places the pivot at position ``i+1``.

Quicksort
=========

The main ``CLRS.Ch07.Quicksort`` module implements the recursive algorithm
using ``pts_to_range`` to split array ownership at the pivot position for
the two recursive calls.

Specification
~~~~~~~~~~~~~

The ``sorted`` predicate and ``clrs_partition_pred`` define the core
specifications used in the loop invariant:

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.Quicksort.fst
   :language: fstar
   :start-after: //SNIPPET_START: sorted
   :end-before: //SNIPPET_END: sorted

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.Quicksort.fst
   :language: fstar
   :start-after: //SNIPPET_START: clrs_partition_pred
   :end-before: //SNIPPET_END: clrs_partition_pred

The CLRS partition function operates on a sub-range ``A[lo..hi)`` using
``pts_to_range``. The postcondition splits the array into three regions
(left, pivot, right) with appropriate bounds:

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.Quicksort.fst
   :language: pulse
   :start-after: //SNIPPET_START: clrs_partition_sig
   :end-before: //SNIPPET_END: clrs_partition_sig

Recursive Sort
~~~~~~~~~~~~~~

The recursive quicksort threads a ghost tick counter through all calls,
proving both correctness and the O(n²) worst-case bound:

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.Quicksort.fst
   :language: pulse
   :start-after: //SNIPPET_START: clrs_quicksort_with_ticks_sig
   :end-before: //SNIPPET_END: clrs_quicksort_with_ticks_sig

After partition splits the array at pivot position ``p``, the left half
``A[lo..p)`` and right half ``A[p+1..hi)`` are sorted recursively. The
ghost proof function ``quicksort_proof`` combines three facts — both halves
are sorted, they are permutations of the originals, and the pivot separates
their value ranges — to re-join them into a single sorted range.

Top-Level API
~~~~~~~~~~~~~

The user-facing ``quicksort`` function converts ``pts_to`` to
``pts_to_range``, computes ghost bounds via ``seq_min``/``seq_max``, calls
the recursive sort, and converts back:

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.Quicksort.fst
   :language: pulse
   :start-after: //SNIPPET_START: quicksort_sig
   :end-before: //SNIPPET_END: quicksort_sig

Complexity
==========

Worst-Case Analysis
~~~~~~~~~~~~~~~~~~~

The pure F\* module ``Quicksort.Complexity`` defines the worst-case
recurrence ``T(n) = T(n-1) + (n-1)`` and proves its closed form:

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.Quicksort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: worst_case_comparisons
   :end-before: //SNIPPET_END: worst_case_comparisons

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.Quicksort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: worst_case_bound
   :end-before: //SNIPPET_END: worst_case_bound

The maximality theorem shows that any partition split is bounded by the
worst case:

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.Quicksort.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: partition_split_bounded
   :end-before: //SNIPPET_END: partition_split_bounded

Quadratic Bound
~~~~~~~~~~~~~~~

The ``Quicksort`` module also defines the quadratic complexity bound
predicate used in the postcondition:

.. literalinclude:: ../ch07-quicksort/CLRS.Ch07.Quicksort.fst
   :language: fstar
   :start-after: //SNIPPET_START: complexity_bounded_quadratic
   :end-before: //SNIPPET_END: complexity_bounded_quadratic

The postcondition says: the final counter minus the initial is at most
``n*(n-1)/2`` where ``n = hi - lo``. This is the standard worst-case
bound for quicksort (CLRS §7.4).

Proof Techniques Summary
=========================

1. **Bound tracking with ``between_bounds``**: The recursive quicksort
   threads ghost lower and upper bounds through calls. The partition
   ensures ``lb ≤ pivot ≤ rb`` and the sub-arrays inherit tightened
   bounds, allowing ``lemma_sorted_append`` to combine sorted halves.

2. **``pts_to_range`` splitting**: Pulse's ``pts_to_range_split`` and
   ``pts_to_range_join`` are used to hand sub-array ownership to
   recursive calls and reassemble the result.

3. **Ghost proof functions**: The ``quicksort_proof`` ghost function
   performs the combine step (joining sorted sub-arrays) purely at the
   proof level, with no runtime cost.

4. **Convexity of the recurrence**: The ``sum_of_parts_bound`` lemma
   proves that ``T(a) + T(b) ≤ T(a+b)`` by induction, establishing
   that the worst-case partition is always the most unbalanced split.
