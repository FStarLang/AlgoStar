# Chapter 2: Getting Started - Sorting Algorithms

This chapter implements fundamental sorting algorithms from CLRS in Pulse with full functional correctness proofs.

## Implemented Algorithms

### InsertionSort (`CLRS.Ch02.InsertionSort.fst`)

In-place sorting using the insertion sort algorithm.

**Algorithm (CLRS 2.1):**
```
for j = 1 to n-1:
    key = A[j]
    i = j - 1
    while i >= 0 and A[i] > key:
        A[i+1] = A[i]
        i = i - 1
    A[i+1] = key
```

**Verified Properties:**
- Output sequence is sorted: `∀ i ≤ j. s[i] ≤ s[j]`
- Output is permutation of input (same elements)
- Memory safety via separation logic

**Signature:**
```pulse
fn insertion_sort (a: A.array int) (len: SZ.t) (#s0: erased (Seq.seq int))
  requires A.pts_to a s0 ** pure (SZ.v len == Seq.length s0)
  ensures exists* s. A.pts_to a s ** pure (sorted s /\ is_permutation s0 s)
```

### MergeSort (`CLRS.Ch02.MergeSort.fst`)

Divide-and-conquer sorting using auxiliary arrays for merging.

**Algorithm (CLRS 2.3):**
```
merge_sort(A, p, r):
  if p < r:
    q = (p + r) / 2
    merge_sort(A, p, q)
    merge_sort(A, q+1, r)
    merge(A, p, q, r)
```

**Verified Properties:**
- Output sequence is sorted
- Output is permutation of input
- Temporary arrays properly allocated and freed

**Signature:**
```pulse
fn merge_sort (a: A.array int) (n: SZ.t) (#s0: erased (Seq.seq int))
  requires A.pts_to a s0 ** pure (SZ.v n == Seq.length s0)
  ensures exists* s. A.pts_to a s ** pure (sorted s /\ is_permutation s0 s)
```

## Building

```bash
cd /home/nswamy/workspace/clrs/ch02-getting-started
make
```

## Dependencies

- Pulse.Lib.Pervasives
- Pulse.Lib.Array
- Pulse.Lib.Reference
- FStar.SizeT
- FStar.Seq

## References

- CLRS Chapter 2: Getting Started
- Pulse examples: `Quicksort.Base.fst`, `MSort.Base.fst`
