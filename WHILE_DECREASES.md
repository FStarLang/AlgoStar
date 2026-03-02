# While Loop Decreases Clauses — Status

## Summary

**130 of ~153 while loops** now have `decreases` clauses. 20 are marked `// TODO: decreases`
(flag-based loops, proof interference, or complex measures). 3 have no loop (spec-only).

All 20 chapters verify with `make -j8`.

## Key Technical Notes

1. **BoundedIntegers interference:** When `Pulse.Lib.BoundedIntegers` is open, use
   `Prims.op_Subtraction` and `Prims.op_Addition` instead of `-`/`+` in decreases expressions.
2. **NuWhile `with` shift:** After Pulse commit `26a5bb640` (NuWhile-only encoding), `with`
   bindings after while loops need an extra `_b` variable at the front for the condition boolean.
3. **Proof interference:** Some decreases clauses break existing proofs by changing SMT context.
   In these cases, the decreases is removed and marked `// TODO: decreases`.

## Overview

Pulse now supports `decreases` clauses for while loops. This plan catalogs
all ~153 while loops in AutoCLRS and specifies the decreases clause for each.

**Syntax:** The `decreases` clause goes after `invariant` and before `{`:
```pulse
while (cond)
invariant exists* ... . ...
decreases (SZ.v n - SZ.v !i)
{
  ...
}
```

## Categories

| Category | Count | Pattern |
|----------|-------|---------|
| Simple counter up (`!i <^ n`) | ~95 | `decreases (SZ.v n - SZ.v !i)` |
| Counter down (`!i >^ 0sz`) | 3 | `decreases (SZ.v !i)` |
| Boolean flag (`!go`) | ~15 | Underlying counter from invariant |
| Compound (`&& / \|\|`) | ~15 | Counter component or lexicographic |
| Path/tree traversal | ~10 | `decreases (SZ.v t.cap - SZ.v !current)` or depth |
| Fuel-bounded | ~5 | Fuel variable |
| Misc | ~10 | Per-loop analysis |

---

## Per-chapter catalog

### ch02-getting-started (4 loops)

- [ ] `CLRS.Ch02.InsertionSort.fst:113` — `while (!j <^ len)`
  - `decreases (SZ.v len - SZ.v !j)`
- [ ] `CLRS.Ch02.InsertionSort.fst:147` — `while (!cont)` (inner loop, j decreases toward 0)
  - `decreases (SZ.v !j)`
- [ ] `CLRS.Ch02.MergeSort.fst:312` — `while (!i <^ len)`
  - `decreases (SZ.v len - SZ.v !i)`
- [ ] `CLRS.Ch02.MergeSort.fst:451` — `while (!i <^ l1 || !j <^ l2)`
  - `decreases ((SZ.v l1 - SZ.v !i) + (SZ.v l2 - SZ.v !j))`

### ch04-divide-conquer (5 loops)

- [ ] `CLRS.Ch04.BinarySearch.fst:115` — `while (!lo <^ !hi && not !found)`
  - `decreases (SZ.v !hi - SZ.v !lo)`
- [ ] `CLRS.Ch04.MatrixMultiply.fst:133` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch04.MatrixMultiply.fst:153` — `while (!j <^ n)`
  - `decreases (SZ.v n - SZ.v !j)`
- [ ] `CLRS.Ch04.MatrixMultiply.fst:184` — `while (!k <^ n)`
  - `decreases (SZ.v n - SZ.v !k)`
- [ ] `CLRS.Ch04.MaxSubarray.Kadane.fst:72` — `while (!i <^ len)`
  - `decreases (SZ.v len - SZ.v !i)`

### ch06-heapsort (2 loops)

- [ ] `CLRS.Ch06.Heap.fst:517` — `while (!i >^ 0sz)`
  - `decreases (SZ.v !i)`
- [ ] `CLRS.Ch06.Heap.fst:724` — `while (!heap_sz >^ 1sz)`
  - `decreases (SZ.v !heap_sz)`

### ch07-quicksort (1 loop)

- [ ] `CLRS.Ch07.Quicksort.fst:256` — `while (let vj = !j; vj < hi - 1)`
  - `decreases (SZ.v hi - 1 - SZ.v !j)` (hi is immutable)

### ch08-linear-sorting (6 loops)

- [ ] `CLRS.Ch08.CountingSort.fst:66` — `while (!j <^ n)`
  - `decreases (SZ.v n - SZ.v !j)`
- [ ] `CLRS.Ch08.CountingSort.fst:95` — `while (!cur_v <=^ k_val)`
  - `decreases (SZ.v k_val - SZ.v !cur_v + 1)`
- [ ] `CLRS.Ch08.CountingSort.fst:127` — `while (!w <^ cnt_sz)`
  - `decreases (SZ.v cnt_sz - SZ.v !w)`
- [ ] `CLRS.Ch08.CountingSort.Stable.fst:91` — `while (let vj = !j; vj <^ len)`
  - `decreases (SZ.v len - SZ.v !j)`
- [ ] `CLRS.Ch08.CountingSort.Stable.fst:141` — `while (let vi = !i; vi <=^ k_val)`
  - `decreases (SZ.v k_val - SZ.v !i + 1)`
- [ ] `CLRS.Ch08.CountingSort.Stable.fst:200` — `while (let vdone = !done; not vdone)` (j decreases from len toward 0)
  - `decreases (SZ.v !j + 1)` (j is SizeT counting down; done=true when j reaches 0)

### ch09-order-statistics (14 loops)

- [ ] `CLRS.Ch09.MinMax.fst:80` — `while (!i <^ len)`
  - `decreases (SZ.v len - SZ.v !i)`
- [ ] `CLRS.Ch09.MinMax.fst:142` — `while (!i <^ len)`
  - `decreases (SZ.v len - SZ.v !i)`
- [ ] `CLRS.Ch09.PartialSelectionSort.fst:169` — `while (!i <^ len)`
  - `decreases (SZ.v len - SZ.v !i)`
- [ ] `CLRS.Ch09.PartialSelectionSort.fst:240` — `while (!round <^ k)`
  - `decreases (SZ.v k - SZ.v !round)`
- [ ] `CLRS.Ch09.PartialSelectionSort.fst:328` — `while (!i <^ len)`
  - `decreases (SZ.v len - SZ.v !i)`
- [ ] `CLRS.Ch09.PartialSelectionSort.fst:401` — `while (!round <^ k)`
  - `decreases (SZ.v k - SZ.v !round)`
- [ ] `CLRS.Ch09.Quickselect.fst:156` — `while (let vj = !j_ref; vj <^ hi_m1)`
  - `decreases (SZ.v hi_m1 - SZ.v !j_ref)`
- [ ] `CLRS.Ch09.Quickselect.fst:307` — `while (!go)` (binary-search style: hi-lo narrows)
  - `decreases (SZ.v !hi - SZ.v !lo)`
- [ ] `CLRS.Ch09.Quickselect.fst:476` — `while (!go)` (same pattern)
  - `decreases (SZ.v !hi - SZ.v !lo)`
- [ ] `CLRS.Ch09.SimultaneousMinMax.fst:109` — `while (!i <^ len)`
  - `decreases (SZ.v len - SZ.v !i)`
- [ ] `CLRS.Ch09.SimultaneousMinMax.fst:191` — `while (let vi = !i; vi <^ len_m1)`
  - `decreases (SZ.v len_m1 - SZ.v !i)`
- [ ] `CLRS.Ch09.SimultaneousMinMax.fst:284` — `while (!i <^ len)`
  - `decreases (SZ.v len - SZ.v !i)`
- [ ] `CLRS.Ch09.SimultaneousMinMax.fst:382` — `while (let vi = !i; vi <^ len_m1)`
  - `decreases (SZ.v len_m1 - SZ.v !i)`

### ch11-hash-tables (3 loops)

- [ ] `CLRS.Ch11.HashTable.fst:309` — `while (not vdone && vi <^ size)` (linear probe search)
  - `decreases (SZ.v size - SZ.v !i)`
- [ ] `CLRS.Ch11.HashTable.fst:420` — `while (not vdone && vi <^ size)` (linear probe insert)
  - `decreases (SZ.v size - SZ.v !i)`
- [ ] `CLRS.Ch11.HashTable.fst:524` — `while (not vdone && vi <^ size)` (linear probe delete)
  - `decreases (SZ.v size - SZ.v !i)`

### ch12-bst (7 loops)

- [ ] `CLRS.Ch12.BSTArray.Delete.fst:115` — `while (!go)` (tree_minimum: walks left children)
  - `decreases (SZ.v t.cap - SZ.v !x)` (x increases toward leaves)
- [ ] `CLRS.Ch12.BSTArray.Delete.fst:219` — `while (!go)` (tree_maximum: walks right children)
  - `decreases (SZ.v t.cap - SZ.v !x)` (x increases toward leaves)
- [ ] `CLRS.Ch12.BSTArray.Delete.fst:340` — `while (vc > 0 && is_right_child)` (walk up right ancestors)
  - `decreases (SZ.v !current)` (current decreases via parent = (c-1)/2)
- [ ] `CLRS.Ch12.BSTArray.Delete.fst:470` — `while (vc > 0 && is_left_child)` (walk up left ancestors)
  - `decreases (SZ.v !current)` (current decreases via parent)
- [ ] `CLRS.Ch12.BSTArray.Delete.fst:728` — `while (vc < cap && not found)` (tree search)
  - `decreases (SZ.v t.cap - SZ.v !current)`
- [ ] `CLRS.Ch12.BSTArray.fst:342` — `while (vc < cap && not found)` (tree search)
  - `decreases (SZ.v t.cap - SZ.v !current)`
- [ ] `CLRS.Ch12.BSTArray.fst:504` — `while (vc < cap && not done)` (tree insert)
  - `decreases (SZ.v t.cap - SZ.v !current)`

### ch15-dynamic-programming (12 loops)

- [ ] `CLRS.Ch15.LCS.fst:215` — `while (!i <=^ m)`
  - `decreases (SZ.v m - SZ.v !i + 1)`
- [ ] `CLRS.Ch15.LCS.fst:234` — `while (!j <=^ n)`
  - `decreases (SZ.v n - SZ.v !j + 1)`
- [ ] `CLRS.Ch15.MatrixChain.Extended.fst:281` — `while (!l <=^ n)`
  - `decreases (SZ.v n - SZ.v !l + 1)`
- [ ] `CLRS.Ch15.MatrixChain.Extended.fst:304` — `while (!i <^ n - vl + 1sz)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch15.MatrixChain.Extended.fst:339` — `while (!k <^ j)`
  - `decreases (SZ.v j - SZ.v !k)`
- [ ] `CLRS.Ch15.MatrixChain.fst:154` — `while (!l <=^ n)`
  - `decreases (SZ.v n - SZ.v !l + 1)`
- [ ] `CLRS.Ch15.MatrixChain.fst:174` — `while (!i <^ n - vl + 1sz)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch15.MatrixChain.fst:205` — `while (!k <^ j)`
  - `decreases (SZ.v j - SZ.v !k)`
- [ ] `CLRS.Ch15.RodCutting.Extended.fst:405` — `while (!j <=^ n)`
  - `decreases (SZ.v n - SZ.v !j + 1)`
- [ ] `CLRS.Ch15.RodCutting.Extended.fst:433` — `while (!i <=^ vj)`
  - `decreases (SZ.v vj - SZ.v !i + 1)`
- [ ] `CLRS.Ch15.RodCutting.fst:198` — `while (!j <=^ n)`
  - `decreases (SZ.v n - SZ.v !j + 1)`
- [ ] `CLRS.Ch15.RodCutting.fst:218` — `while (!i <=^ vj)`
  - `decreases (SZ.v vj - SZ.v !i + 1)`

### ch16-greedy (3 loops)

- [ ] `CLRS.Ch16.ActivitySelection.fst:131` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch16.Huffman.fst:281` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch16.Huffman.fst:342` — `while (!iter <^ n_minus_1)`
  - `decreases (SZ.v n_minus_1 - SZ.v !iter)`

### ch21-disjoint-sets (5 loops)

- [ ] `CLRS.Ch21.UnionFind.fst:368` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch21.UnionFind.fst:445` — `while (!go)` (find: walks parent pointers toward root)
  - `decreases (SZ.v n - SZ.v !x)` (distance to root, or use depth from invariant)
- [ ] `CLRS.Ch21.UnionFind.FullCompress.fst:293` — `while (curr != root && count < n)`
  - `decreases (SZ.v n - SZ.v !count)`
- [ ] `CLRS.Ch21.UnionFind.FullCompress.fst:384` — `while (!go)` (find_set walk #1)
  - `decreases (SZ.v n - SZ.v !count)` (bounded by array size)
- [ ] `CLRS.Ch21.UnionFind.FullCompress.fst:482` — `while (!go)` (find_set walk #2, compression pass)
  - `decreases (SZ.v n - SZ.v !count)` (bounded by array size)

### ch22-elementary-graph (18 loops)

- [ ] `CLRS.Ch22.IterativeBFS.fst:103` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch22.IterativeBFS.fst:129` — `while (!round <^ n)`
  - `decreases (SZ.v n - SZ.v !round)`
- [ ] `CLRS.Ch22.IterativeBFS.fst:153` — `while (!u <^ n)`
  - `decreases (SZ.v n - SZ.v !u)`
- [ ] `CLRS.Ch22.IterativeBFS.fst:185` — `while (!v <^ n)`
  - `decreases (SZ.v n - SZ.v !v)`
- [ ] `CLRS.Ch22.KahnTopologicalSort.fst:283` — `while (!v <^ n)`
  - `decreases (SZ.v n - SZ.v !v)`
- [ ] `CLRS.Ch22.KahnTopologicalSort.fst:378` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch22.KahnTopologicalSort.fst:400` — `while (!j <^ n)`
  - `decreases (SZ.v n - SZ.v !j)`
- [ ] `CLRS.Ch22.KahnTopologicalSort.fst:470` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch22.KahnTopologicalSort.fst:547` — `while (!queue_head <^ !queue_tail)` (tail only increases)
  - `decreases (SZ.v n - SZ.v !queue_head)` (head advances, bounded by n)
- [ ] `CLRS.Ch22.QueueBFS.fst:476` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch22.QueueBFS.fst:519` — `while (let vh = !q_head; let vt = !q_tail; vh < vt)`
  - `decreases (SZ.v !q_tail - SZ.v !q_head)` (head advances, tail constant in BFS)
- [ ] `CLRS.Ch22.QueueBFS.fst:570` — `while (!v <^ n)`
  - `decreases (SZ.v n - SZ.v !v)`
- [ ] `CLRS.Ch22.StackDFS.fst:586` — `while (let vtop = !stack_top; vtop > 0sz)`
  - `decreases (SZ.v !stack_top)` — **tricky**: stack_top can increase then decrease; need total work argument or fuel. May need `n * n - SZ.v !time` or a ghost fuel counter.
- [ ] `CLRS.Ch22.StackDFS.fst:638` — `while (!scan <^ n && !found_white)` (inner scan)
  - `decreases (SZ.v n - SZ.v !scan)`
- [ ] `CLRS.Ch22.StackDFS.fst:949` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch22.StackDFS.fst:983` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch22.StackDFS.fst:1026` — `while (!s <^ n)`
  - `decreases (SZ.v n - SZ.v !s)`

### ch23-mst (16 loops)

- [ ] `CLRS.Ch23.Kruskal.fst:213` — `while (!steps <^ n)`
  - `decreases (SZ.v n - SZ.v !steps)`
- [ ] `CLRS.Ch23.Kruskal.fst:407` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch23.Kruskal.fst:436` — `while (!round <^ max_rounds)`
  - `decreases (SZ.v max_rounds - SZ.v !round)`
- [ ] `CLRS.Ch23.Kruskal.fst:459` — `while (!ui <^ n)`
  - `decreases (SZ.v n - SZ.v !ui)`
- [ ] `CLRS.Ch23.Kruskal.fst:477` — `while (!vi <^ n)`
  - `decreases (SZ.v n - SZ.v !vi)`
- [ ] `CLRS.Ch23.Kruskal.Complexity.fst:211` — `while (!steps <^ n)`
  - `decreases (SZ.v n - SZ.v !steps)`
- [ ] `CLRS.Ch23.Kruskal.Complexity.fst:310` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch23.Kruskal.Complexity.fst:343` — `while (!round <^ max_rounds)`
  - `decreases (SZ.v max_rounds - SZ.v !round)`
- [ ] `CLRS.Ch23.Kruskal.Complexity.fst:372` — `while (!ui <^ n)`
  - `decreases (SZ.v n - SZ.v !ui)`
- [ ] `CLRS.Ch23.Kruskal.Complexity.fst:400` — `while (!vi <^ n)`
  - `decreases (SZ.v n - SZ.v !vi)`
- [ ] `CLRS.Ch23.Prim.fst:228` — `while (let v_iter = !iter; v_iter <^ n)`
  - `decreases (SZ.v n - SZ.v !iter)`
- [ ] `CLRS.Ch23.Prim.fst:253` — `while (let v_find_i = !find_i; v_find_i <^ n)`
  - `decreases (SZ.v n - SZ.v !find_i)`
- [ ] `CLRS.Ch23.Prim.fst:304` — `while (let v_update_i = !update_i; v_update_i <^ n)`
  - `decreases (SZ.v n - SZ.v !update_i)`
- [ ] `CLRS.Ch23.Prim.Complexity.fst:211` — `while (let v_iter = !iter; v_iter <^ n)`
  - `decreases (SZ.v n - SZ.v !iter)`
- [ ] `CLRS.Ch23.Prim.Complexity.fst:239` — `while (let v_find_i = !find_i; v_find_i <^ n)`
  - `decreases (SZ.v n - SZ.v !find_i)`
- [ ] `CLRS.Ch23.Prim.Complexity.fst:304` — `while (let v_update_i = !update_i; v_update_i <^ n)`
  - `decreases (SZ.v n - SZ.v !update_i)`

### ch24-sssp (20 loops)

- [ ] `CLRS.Ch24.BellmanFord.fst:328` — `while (let vi = !init_i; vi <^ n)`
  - `decreases (SZ.v n - SZ.v !init_i)`
- [ ] `CLRS.Ch24.BellmanFord.fst:359` — `while (let vround = !round; vround <^ n)`
  - `decreases (SZ.v n - SZ.v !round)`
- [ ] `CLRS.Ch24.BellmanFord.fst:379` — `while (let vu = !u; vu <^ n)`
  - `decreases (SZ.v n - SZ.v !u)`
- [ ] `CLRS.Ch24.BellmanFord.fst:402` — `while (let vv = !v; vv <^ n)`
  - `decreases (SZ.v n - SZ.v !v)`
- [ ] `CLRS.Ch24.BellmanFord.fst:472` — `while (let vcu = !cu; vcu <^ n)`
  - `decreases (SZ.v n - SZ.v !cu)`
- [ ] `CLRS.Ch24.BellmanFord.fst:497` — `while (let vcv = !cv; vcv <^ n)`
  - `decreases (SZ.v n - SZ.v !cv)`
- [ ] `CLRS.Ch24.BellmanFord.Complexity.Instrumented.fst:175` — `while (let vi = !init_i; vi <^ n)`
  - `decreases (SZ.v n - SZ.v !init_i)`
- [ ] `CLRS.Ch24.BellmanFord.Complexity.Instrumented.fst:207` — `while (let vround = !round; vround <^ n)`
  - `decreases (SZ.v n - SZ.v !round)`
- [ ] `CLRS.Ch24.BellmanFord.Complexity.Instrumented.fst:229` — `while (let vu = !u; vu <^ n)`
  - `decreases (SZ.v n - SZ.v !u)`
- [ ] `CLRS.Ch24.BellmanFord.Complexity.Instrumented.fst:254` — `while (let vv = !v; vv <^ n)`
  - `decreases (SZ.v n - SZ.v !v)`
- [ ] `CLRS.Ch24.BellmanFord.Complexity.Instrumented.fst:318` — `while (let vcu = !cu; vcu <^ n)`
  - `decreases (SZ.v n - SZ.v !cu)`
- [ ] `CLRS.Ch24.BellmanFord.Complexity.Instrumented.fst:344` — `while (let vcv = !cv; vcv <^ n)`
  - `decreases (SZ.v n - SZ.v !cv)`
- [ ] `CLRS.Ch24.Dijkstra.fst:320` — `while (let vi = !i; vi <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch24.Dijkstra.fst:414` — `while (let vi = !init_i; vi <^ n)`
  - `decreases (SZ.v n - SZ.v !init_i)`
- [ ] `CLRS.Ch24.Dijkstra.fst:453` — `while (let vround = !round; vround <^ n)`
  - `decreases (SZ.v n - SZ.v !round)`
- [ ] `CLRS.Ch24.Dijkstra.fst:504` — `while (let vv = !v; vv <^ n)`
  - `decreases (SZ.v n - SZ.v !v)`
- [ ] `CLRS.Ch24.Dijkstra.Complexity.fst:171` — `while (let vi = !i; vi <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch24.Dijkstra.Complexity.fst:255` — `while (let vi = !init_i; vi <^ n)`
  - `decreases (SZ.v n - SZ.v !init_i)`
- [ ] `CLRS.Ch24.Dijkstra.Complexity.fst:288` — `while (let vround = !round; vround <^ n)`
  - `decreases (SZ.v n - SZ.v !round)`
- [ ] `CLRS.Ch24.Dijkstra.Complexity.fst:322` — `while (let vv = !v; vv <^ n)`
  - `decreases (SZ.v n - SZ.v !v)`

### ch25-apsp (6 loops)

- [ ] `CLRS.Ch25.FloydWarshall.fst:126` — `while (!k <^ n)`
  - `decreases (SZ.v n - SZ.v !k)`
- [ ] `CLRS.Ch25.FloydWarshall.fst:142` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch25.FloydWarshall.fst:163` — `while (!j <^ n)`
  - `decreases (SZ.v n - SZ.v !j)`
- [ ] `CLRS.Ch25.FloydWarshall.Complexity.fst:85` — `while (!k <^ n)`
  - `decreases (SZ.v n - SZ.v !k)`
- [ ] `CLRS.Ch25.FloydWarshall.Complexity.fst:103` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch25.FloydWarshall.Complexity.fst:124` — `while (!j <^ n)`
  - `decreases (SZ.v n - SZ.v !j)`

### ch26-max-flow (11 loops)

- [ ] `CLRS.Ch26.MaxFlow.fst:395` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch26.MaxFlow.fst:557` — `while (!v <^ n)`
  - `decreases (SZ.v n - SZ.v !v)`
- [ ] `CLRS.Ch26.MaxFlow.fst:642` — `while (vh < vt)` (BFS queue drain)
  - `decreases (SZ.v !q_tail - SZ.v !q_head)`
- [ ] `CLRS.Ch26.MaxFlow.fst:723` — `while (current != source)` (augmenting path: walk predecessors)
  - `decreases (SZ.v nn - SZ.v !steps)` (need fuel counter or predecessor chain length)
- [ ] `CLRS.Ch26.MaxFlow.fst:810` — `while (current != source)` (same pattern)
  - `decreases (SZ.v nn - SZ.v !steps)`
- [ ] `CLRS.Ch26.MaxFlow.fst:907` — `while (vr && vi <^ nn)` (verification loop)
  - `decreases (SZ.v nn - SZ.v !i)`
- [ ] `CLRS.Ch26.MaxFlow.fst:956` — `while (vr && vi <^ nn)` (verification loop)
  - `decreases (SZ.v nn - SZ.v !i)`
- [ ] `CLRS.Ch26.MaxFlow.fst:1008` — `while (!v <^ n)`
  - `decreases (SZ.v n - SZ.v !v)`
- [ ] `CLRS.Ch26.MaxFlow.fst:1066` — `while (vr && vu <^ n)` (verification loop)
  - `decreases (SZ.v n - SZ.v !u_idx)`
- [ ] `CLRS.Ch26.MaxFlow.fst:1154` — `while (!i <^ nn)`
  - `decreases (SZ.v nn - SZ.v !i)`
- [ ] `CLRS.Ch26.MaxFlow.fst:1224` — `while (!continue_loop && !iters <^ fuel)`
  - `decreases (SZ.v fuel - SZ.v !iters)`

### ch31-number-theory (3 loops)

- [ ] `CLRS.Ch31.GCD.fst:200` — `while (!b >^ 0sz)`
  - `decreases (SZ.v !b)`
- [ ] `CLRS.Ch31.ModExp.fst:179` — `while (let ve = !exp; ve > 0)` (exp halved each iteration)
  - `decreases (!exp)` (integer, halved each time)
- [ ] `CLRS.Ch31.ModExpLR.fst:105` — `while (let vi = !i; vi >= 0)` (i decrements)
  - `decreases (!i + 1)` (i is signed int, counts down to -1)

### ch32-string-matching (10 loops)

- [ ] `CLRS.Ch32.KMP.fst:103` — `while (!q <^ m)`
  - `decreases (SZ.v m - SZ.v !q)`
- [ ] `CLRS.Ch32.KMP.fst:135` — `while (not !done_inner)` (KMP failure function inner loop: q decreases)
  - `decreases (SZ.v !q)` (q decreases via pi[q] each iteration)
- [ ] `CLRS.Ch32.KMP.fst:285` — `while (!i <^ n)`
  - `decreases (SZ.v n - SZ.v !i)`
- [ ] `CLRS.Ch32.KMP.fst:316` — `while (not !done_follow)` (KMP search inner loop: q decreases)
  - `decreases (SZ.v !q)` (q decreases via pi[q])
- [ ] `CLRS.Ch32.NaiveStringMatch.fst:154` — `while (!s <=^ (n -^ m))`
  - `decreases (SZ.v n - SZ.v m - SZ.v !s + 1)`
- [ ] `CLRS.Ch32.NaiveStringMatch.fst:176` — `while (!j <^ m && !all_match)` (inner comparison)
  - `decreases (SZ.v m - SZ.v !j)`
- [ ] `CLRS.Ch32.RabinKarp.fst:113` — `while (!i <^ len)`
  - `decreases (SZ.v len - SZ.v !i)`
- [ ] `CLRS.Ch32.RabinKarp.fst:150` — `while (!i <^ exp)`
  - `decreases (SZ.v exp - SZ.v !i)`
- [ ] `CLRS.Ch32.RabinKarp.fst:218` — `while (!s <=^ max_s)`
  - `decreases (SZ.v max_s - SZ.v !s + 1)`
- [ ] `CLRS.Ch32.RabinKarp.fst:250` — `while (!j <^ m && !verified = 1)` (inner verification)
  - `decreases (SZ.v m - SZ.v !j)`

### ch33-comp-geometry (5 loops)

- [ ] `CLRS.Ch33.GrahamScan.fst:320` — `while (!i <^ len)`
  - `decreases (SZ.v len - SZ.v !i)`
- [ ] `CLRS.Ch33.GrahamScan.fst:415` — `while (!keep_going)` (pop while not left turn: stack shrinks)
  - `decreases (SZ.v !t)` (t is the stack top index, decreasing)
- [ ] `CLRS.Ch33.JarvisMarch.fst:495` — `while (!i <^ len)`
  - `decreases (SZ.v len - SZ.v !i)`
- [ ] `CLRS.Ch33.JarvisMarch.fst:553` — `while (!j <^ len)`
  - `decreases (SZ.v len - SZ.v !j)`
- [ ] `CLRS.Ch33.JarvisMarch.fst:628` — `while (!running)` (Jarvis march: h increases toward hull size)
  - `decreases (jarvis_march_spec sxs sys - SZ.v !h)` (from invariant: h approaches hull size)

### ch35-approximation (2 loops)

- [ ] `CLRS.Ch35.VertexCover.fst:205` — `while (!u <^ n)`
  - `decreases (SZ.v n - SZ.v !u)`
- [ ] `CLRS.Ch35.VertexCover.fst:230` — `while (!v <^ n)`
  - `decreases (SZ.v n - SZ.v !v)`

---

## Approach

### Phase 1: Simple counter loops (~95 loops)
These are mechanical: add `decreases (SZ.v bound - SZ.v !counter)` after invariant.
For `<=` conditions, use `+ 1` offset: `decreases (SZ.v bound - SZ.v !counter + 1)`.

### Phase 2: Flag-based loops (~15 loops)
Identify the actual decreasing quantity from the invariant and loop body.
Common patterns: binary search narrowing, tree depth descent, stack height.

### Phase 3: Complex/compound loops (~15 loops)
Hash table probing (bounded by size), KMP inner loops (bounded by q), etc.

### Phase 4: Tricky loops (~5 loops)
- StackDFS main loop: stack grows and shrinks; need global `time` counter
- Jarvis march: needs spec-level measure
- MaxFlow augmenting path walks: need fuel/step counter
- ModExpLR: signed integer counting down (may need special handling)

### Notes
- For `<=` conditions, the measure must be `bound - counter + 1` (not just `bound - counter`)
  since the loop can execute one more time when counter == bound.
- For flag loops, the `!flag` read in the condition should be fine with the new encoding
  since booleans have no preconditions.
- Nested loops: inner loops get their own decreases clauses independently.
- The `value_of` pattern may be needed if we can only read ghost refs.
