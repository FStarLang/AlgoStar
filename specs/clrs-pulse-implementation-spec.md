# CLRS Algorithms Implementation in Pulse - Technical Design Document

| Document Metadata      | Details                                   |
| ---------------------- | ----------------------------------------- |
| Author(s)              | Nikhil Swamy                              |
| Status                 | Draft (WIP)                               |
| Team / Owner           | FStar/Pulse Team                          |
| Created / Last Updated | 2026-02-05                                |

---

## 1. Executive Summary

This RFC proposes implementing verified algorithms and data structures from CLRS (Introduction to Algorithms, 3rd Edition) using Pulse, the separation-logic-based imperative language embedded in F*. The 30 chapter directories have been scaffolded but contain no implementations. We will implement **~120 algorithms** and **~30 data structures** across **4 phases**, starting with foundational sorting and elementary data structures, then advancing to graphs, dynamic programming, and specialized algorithms. Each implementation will include formal verification of correctness properties (sortedness, invariant maintenance, permutation preservation) and memory safety via separation logic.

**Key Value:** A comprehensive library of verified classic algorithms demonstrating Pulse's capabilities for low-level systems programming with machine-checked correctness proofs.

---

## 2. Context and Motivation

### 2.1 Current State

- **Directory Structure:** 30 chapter directories exist under `/home/nswamy/workspace/clrs/` (ch02-ch35) - all currently empty
- **Research:** Comprehensive implementation plan exists at `research/docs/2026-02-05-clrs-algorithms-pulse-implementation-plan.md` cataloging all algorithms
- **Reference Material:** CLRS 3rd edition PDF and text available in repository root
- **Supporting Libraries:**
  - `Pulse.Lib.Array` - Array operations with `pts_to` predicates
  - `Pulse.Lib.Reference` - Mutable references
  - `FStar.Seq` - Immutable sequences for specifications
  - `FStar.Seq.Permutation` - Permutation reasoning
  - LowStar buffers and existing verified sorting examples (QuickSort, InsertionSort, MergeSort)

### 2.2 The Problem

- **Educational Gap:** No comprehensive verified algorithm library exists for Pulse/F* covering classic CLRS algorithms
- **Verification Patterns:** Need to establish reusable patterns for proving sorting, data structure invariants, and graph properties
- **Demonstration:** Need showcase implementations proving Pulse's viability for verified systems programming

---

## 3. Goals and Non-Goals

### 3.1 Functional Goals

- [ ] Implement Phase 1 core algorithms: Insertion Sort, Merge Sort, Quicksort, Stack, Queue, Linked List, Heap, BST, Union-Find, BFS, DFS
- [ ] Implement Phase 2 advanced structures: Hash Tables, Red-Black Trees, B-Trees, Dynamic Programming algorithms, MST
- [ ] Implement Phase 3 specialized algorithms: Linear-time sorting, Order statistics, Greedy, Max flow, String matching
- [ ] Implement Phase 4 advanced topics: Augmented structures, Fibonacci heaps, Matrix operations, Computational geometry
- [ ] Verify correctness properties: sortedness, permutation preservation, structural invariants
- [ ] Verify memory safety via separation logic `pts_to` predicates
- [ ] Prove termination for all recursive algorithms
- [ ] Provide documentation (README.md) for each chapter

### 3.2 Non-Goals (Out of Scope)

- [ ] We will NOT implement Chapter 1 (theoretical introduction) or Chapter 3 (asymptotic notation) - purely theoretical
- [ ] We will NOT implement Chapter 17 (amortized analysis) - analysis techniques, not algorithms
- [ ] We will NOT implement Chapter 27 (multithreaded algorithms) - requires different verification model
- [ ] We will NOT implement Chapter 29 (linear programming) - numerical/floating-point challenges
- [ ] We will NOT implement Chapter 34 (NP-completeness) - complexity proofs, not algorithms
- [ ] We will NOT prove formal complexity bounds (O-notation) - focus on functional correctness
- [ ] We will NOT implement randomized variants with probabilistic guarantees initially

---

## 4. Proposed Solution (High-Level Design)

### 4.1 System Architecture Diagram

```mermaid
%%{init: {'theme':'base', 'themeVariables': { 'primaryColor':'#f8f9fa'}}}%%

flowchart TB
    subgraph clrs["CLRS Pulse Library"]
        direction TB
        
        subgraph Phase1["Phase 1: Core Foundations"]
            ch02["ch02: Sorting<br/>InsertionSort, MergeSort"]
            ch10["ch10: Elementary DS<br/>Stack, Queue, LinkedList"]
            ch06["ch06: Heaps<br/>MaxHeap, PriorityQueue"]
            ch12["ch12: BST<br/>Search, Insert, Delete"]
            ch07["ch07: Quicksort<br/>Partition, Sort"]
            ch21["ch21: Disjoint Sets<br/>Union-Find"]
            ch22["ch22: Graphs<br/>BFS, DFS, TopoSort"]
            ch24["ch24: SSSP<br/>Dijkstra, Bellman-Ford"]
        end
        
        subgraph Phase2["Phase 2: Advanced Structures"]
            ch11["ch11: Hash Tables"]
            ch13["ch13: Red-Black Trees"]
            ch15["ch15: Dynamic Programming"]
            ch18["ch18: B-Trees"]
            ch23["ch23: MST<br/>Kruskal, Prim"]
        end
        
        subgraph Phase3["Phase 3: Specialized"]
            ch08["ch08: Linear Sorting"]
            ch09["ch09: Order Statistics"]
            ch16["ch16: Greedy"]
            ch26["ch26: Max Flow"]
            ch31["ch31: Number Theory"]
            ch32["ch32: String Matching"]
            ch33["ch33: Comp Geometry"]
        end
        
        subgraph Phase4["Phase 4: Advanced"]
            ch14["ch14: Augmented DS"]
            ch19["ch19: Fibonacci Heaps"]
            ch25["ch25: APSP"]
            ch28["ch28: Matrix Ops"]
            ch30["ch30: FFT"]
            ch35["ch35: Approximation"]
        end
    end
    
    subgraph libs["Supporting Libraries"]
        pulse_array["Pulse.Lib.Array"]
        pulse_ref["Pulse.Lib.Reference"]
        fstar_seq["FStar.Seq"]
        fstar_perm["FStar.Seq.Permutation"]
    end
    
    Phase1 --> libs
    Phase2 --> Phase1
    Phase3 --> Phase2
    Phase4 --> Phase3
```

### 4.2 Architectural Pattern

**Layered Verification with Separation Logic:**

1. **Specification Layer (F*):** Pure functional specifications using `FStar.Seq`, ghost predicates
2. **Implementation Layer (Pulse):** Imperative implementations with `pts_to` ownership
3. **Proof Layer:** Lemmas connecting implementation state to specification, invariant maintenance

**Example Pattern:**
```pulse
// Specification (Pure F*)
let sorted (s: seq int) = forall i j. i < j ==> index s i <= index s j
let is_permutation (s1 s2: seq int) = FStar.Seq.Permutation.is_permutation s1 s2

// Implementation (Pulse with separation logic)
fn insertion_sort (a: array int) (n: nat)
  requires A.pts_to a #full_perm s0 ** pure (length s0 == n)
  returns _: unit
  ensures exists* s1. A.pts_to a #full_perm s1 ** 
                       pure (sorted s1 /\ is_permutation s0 s1)
```

### 4.3 Key Components

| Component | Responsibility | Technology | Priority |
|-----------|----------------|------------|----------|
| **Common.Predicates** | Shared predicates: `sorted`, `is_permutation`, `heap_property` | Pulse/F* | Critical |
| **Common.ArrayOps** | Verified swap, copy, range operations | Pulse | Critical |
| **ch02-getting-started** | InsertionSort, MergeSort | Pulse | Phase 1 |
| **ch06-heapsort** | MaxHeap, MinHeap, Heapsort, PriorityQueue | Pulse | Phase 1 |
| **ch07-quicksort** | Partition, Quicksort | Pulse | Phase 1 |
| **ch10-elementary-ds** | Stack, Queue, LinkedList | Pulse | Phase 1 |
| **ch12-bst** | BinarySearchTree operations | Pulse | Phase 1 |
| **ch21-disjoint-sets** | Union-Find with path compression | Pulse | Phase 1 |
| **ch22-elementary-graph** | Graph representation, BFS, DFS, TopSort, SCC | Pulse | Phase 1 |
| **ch24-sssp** | Bellman-Ford, Dijkstra, DAG shortest paths | Pulse | Phase 1 |

---

## 5. Detailed Design

### 5.1 Common Verification Predicates

**File:** `common/Predicates.fsti`

```fstar
module CLRS.Common.Predicates

open FStar.Seq

// Sortedness predicate
val sorted (#a:eqtype) (cmp: a -> a -> bool) (s: seq a) : prop

// Permutation predicate
val is_permutation (#a:eqtype) (s1 s2: seq a) : prop

// Heap property (max-heap)
val max_heap_property (s: seq int) (i: nat{i < length s}) : prop

// BST property
val bst_property (#a:eqtype) (cmp: a -> a -> int) (t: tree a) : prop

// Graph predicates
val valid_graph (g: graph) : prop
val path_exists (g: graph) (src dst: vertex) : prop
val shortest_path (g: graph) (src dst: vertex) (dist: nat) : prop
```

### 5.2 Phase 1 Detailed Specifications

#### 5.2.1 Chapter 2: Sorting

**File:** `ch02-getting-started/InsertionSort.pulse`

```pulse
module CLRS.Ch02.InsertionSort

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open CLRS.Common.Predicates

// In-place insertion sort
fn insertion_sort (#t:eqtype) (a: array t) (n: SZ.t) (cmp: t -> t -> bool)
  requires 
    A.pts_to a #full_perm s0 ** 
    pure (SZ.v n == Seq.length s0)
  returns _: unit
  ensures exists* s1. 
    A.pts_to a #full_perm s1 ** 
    pure (sorted cmp s1 /\ is_permutation s0 s1)
```

**Verification Goals:**
- [x] Output sequence is sorted according to comparator
- [x] Output is a permutation of input (same elements)
- [x] In-place: only modifies input array
- [x] Termination: outer loop bounded by n, inner loop bounded by j

**File:** `ch02-getting-started/MergeSort.pulse`

```pulse
fn merge (#t:eqtype) (a: array t) (p q r: SZ.t) (cmp: t -> t -> bool)
  requires 
    A.pts_to a #full_perm s ** 
    pure (SZ.v p <= SZ.v q < SZ.v r <= Seq.length s) **
    pure (sorted cmp (Seq.slice s (SZ.v p) (SZ.v q + 1))) **
    pure (sorted cmp (Seq.slice s (SZ.v q + 1) (SZ.v r + 1)))
  returns _: unit
  ensures exists* s'.
    A.pts_to a #full_perm s' **
    pure (sorted cmp (Seq.slice s' (SZ.v p) (SZ.v r + 1))) **
    pure (is_permutation (Seq.slice s (SZ.v p) (SZ.v r + 1)) 
                          (Seq.slice s' (SZ.v p) (SZ.v r + 1)))

fn merge_sort (#t:eqtype) (a: array t) (p r: SZ.t) (cmp: t -> t -> bool)
  requires A.pts_to a #full_perm s ** pure (SZ.v p <= SZ.v r < Seq.length s)
  returns _: unit
  ensures exists* s'. 
    A.pts_to a #full_perm s' **
    pure (sorted cmp (Seq.slice s' (SZ.v p) (SZ.v r + 1))) **
    pure (is_permutation (Seq.slice s (SZ.v p) (SZ.v r + 1))
                          (Seq.slice s' (SZ.v p) (SZ.v r + 1)))
```

#### 5.2.2 Chapter 6: Heapsort

**File:** `ch06-heapsort/Heap.pulse`

```pulse
module CLRS.Ch06.Heap

// Max-heap representation: array with heap_size
noeq type max_heap = {
  data: array int;
  heap_size: ref SZ.t;
}

// Heap invariant as separation logic predicate
let heap_inv (h: max_heap) (s: erased (seq int)) (sz: erased nat) : slprop =
  A.pts_to h.data #full_perm s **
  R.pts_to h.heap_size (SZ.uint_to_t sz) **
  pure (sz <= Seq.length s) **
  pure (forall (i:nat{i < sz}). max_heap_property (Seq.slice s 0 sz) i)

fn max_heapify (h: max_heap) (i: SZ.t)
  requires heap_inv h s sz ** pure (SZ.v i < sz)
  ensures heap_inv h s' sz ** 
          pure (is_permutation (Seq.slice s 0 sz) (Seq.slice s' 0 sz))

fn build_max_heap (a: array int) (n: SZ.t)
  requires A.pts_to a #full_perm s ** pure (SZ.v n == Seq.length s)
  returns h: max_heap
  ensures heap_inv h s' n ** pure (is_permutation s s')

fn heapsort (a: array int) (n: SZ.t)
  requires A.pts_to a #full_perm s ** pure (SZ.v n == Seq.length s)
  returns _: unit
  ensures exists* s'. A.pts_to a #full_perm s' ** 
                       pure (sorted (<=) s' /\ is_permutation s s')
```

#### 5.2.3 Chapter 10: Elementary Data Structures

**File:** `ch10-elementary-ds/Stack.pulse`

```pulse
module CLRS.Ch10.Stack

// Array-based stack with top pointer
noeq type stack (t:Type) = {
  data: array t;
  top: ref SZ.t;  // Index of next free slot
  capacity: erased nat;
}

let stack_inv (#t:Type) (stk: stack t) (contents: erased (list t)) : slprop =
  exists* s top_v.
    A.pts_to stk.data #full_perm s **
    R.pts_to stk.top top_v **
    pure (SZ.v top_v == List.length contents) **
    pure (SZ.v top_v <= stk.capacity) **
    pure (Seq.length s == stk.capacity) **
    pure (forall (i:nat{i < SZ.v top_v}). 
            Seq.index s i == List.index contents (SZ.v top_v - 1 - i))

fn stack_empty (#t:Type) (stk: stack t)
  requires stack_inv stk contents
  returns b: bool
  ensures stack_inv stk contents ** pure (b <==> contents == [])

fn push (#t:Type) (stk: stack t) (x: t)
  requires stack_inv stk contents ** pure (List.length contents < stk.capacity)
  returns _: unit
  ensures stack_inv stk (x :: contents)

fn pop (#t:Type) (stk: stack t)
  requires stack_inv stk contents ** pure (Cons? contents)
  returns x: t
  ensures stack_inv stk (List.tail contents) ** pure (x == List.hd contents)
```

**File:** `ch10-elementary-ds/Queue.pulse`

```pulse
module CLRS.Ch10.Queue

// Circular buffer queue
noeq type queue (t:Type) = {
  data: array t;
  head: ref SZ.t;
  tail: ref SZ.t;
  capacity: erased nat;
}

fn enqueue (#t:Type) (q: queue t) (x: t)
  requires queue_inv q contents ** pure (List.length contents < q.capacity)
  returns _: unit
  ensures queue_inv q (contents @ [x])

fn dequeue (#t:Type) (q: queue t)
  requires queue_inv q contents ** pure (Cons? contents)
  returns x: t
  ensures queue_inv q (List.tail contents) ** pure (x == List.hd contents)
```

**File:** `ch10-elementary-ds/LinkedList.pulse`

```pulse
module CLRS.Ch10.LinkedList

// Doubly-linked list node
noeq type node (t:Type) = {
  key: t;
  prev: ref (option (ref (node t)));
  next: ref (option (ref (node t)));
}

// List representation with head/tail
noeq type linked_list (t:Type) = {
  head: ref (option (ref (node t)));
  tail: ref (option (ref (node t)));
}

fn list_search (#t:eqtype) (l: linked_list t) (k: t)
  requires list_inv l contents
  returns r: option (ref (node t))
  ensures list_inv l contents ** 
          pure (Some? r <==> List.mem k contents)

fn list_insert (#t:Type) (l: linked_list t) (x: ref (node t))
  requires list_inv l contents ** node_inv x v
  returns _: unit
  ensures list_inv l (v :: contents)

fn list_delete (#t:eqtype) (l: linked_list t) (x: ref (node t))
  requires list_inv l contents ** pure (List.mem (node_key x) contents)
  returns _: unit
  ensures list_inv l (List.filter (fun v -> v <> node_key x) contents)
```

#### 5.2.4 Chapter 12: Binary Search Trees

**File:** `ch12-bst/BinarySearchTree.pulse`

```pulse
module CLRS.Ch12.BST

// BST node with parent pointer
noeq type bst_node (t:Type) = {
  key: t;
  left: ref (option (ref (bst_node t)));
  right: ref (option (ref (bst_node t)));
  parent: ref (option (ref (bst_node t)));
}

// BST invariant: all left descendants < key < all right descendants
let bst_inv (#t:Type) (cmp: t -> t -> int) (root: option (ref (bst_node t))) 
            (contents: erased (set t)) : slprop = ...

fn tree_search (#t:eqtype) (cmp: t -> t -> int) (x: ref (bst_node t)) (k: t)
  requires bst_inv cmp (Some x) contents
  returns r: option (ref (bst_node t))
  ensures bst_inv cmp (Some x) contents ** 
          pure (Some? r <==> Set.mem k contents)

fn tree_insert (#t:Type) (cmp: t -> t -> int) (root: ref (option (ref (bst_node t)))) (z: ref (bst_node t))
  requires bst_inv cmp (!root) contents ** node_owns z k ** pure (not (Set.mem k contents))
  returns _: unit
  ensures bst_inv cmp (!root) (Set.add k contents)

fn tree_delete (#t:eqtype) (cmp: t -> t -> int) (root: ref (option (ref (bst_node t)))) (z: ref (bst_node t))
  requires bst_inv cmp (!root) contents ** pure (Set.mem (node_key z) contents)
  returns _: unit
  ensures bst_inv cmp (!root) (Set.remove (node_key z) contents)

fn inorder_tree_walk (#t:Type) (x: option (ref (bst_node t))) (visit: t -> unit)
  requires bst_inv cmp x contents
  ensures bst_inv cmp x contents  // Read-only traversal
  // Visits nodes in sorted order
```

#### 5.2.5 Chapter 21: Disjoint Sets (Union-Find)

**File:** `ch21-disjoint-sets/UnionFind.pulse`

```pulse
module CLRS.Ch21.UnionFind

// Disjoint set forest with rank
noeq type uf_node = {
  parent: ref (ref uf_node);  // Points to self if root
  rank: ref nat;
}

// Union-find forest invariant
let uf_inv (nodes: list (ref uf_node)) (partition: erased (set (set nat))) : slprop = ...

fn make_set (x: nat)
  requires emp
  returns node: ref uf_node
  ensures uf_node_inv node x ** pure (is_root node)

fn find_set (x: ref uf_node)
  requires uf_node_inv x id
  returns root: ref uf_node
  ensures uf_node_inv x id ** pure (same_set root x)
  // Implements path compression

fn union (x y: ref uf_node)
  requires uf_node_inv x idx ** uf_node_inv y idy
  returns _: unit
  ensures uf_node_inv x idx ** uf_node_inv y idy ** pure (same_set x y)
  // Implements union by rank
```

#### 5.2.6 Chapter 22: Graph Algorithms

**File:** `ch22-elementary-graph/Graph.pulse`

```pulse
module CLRS.Ch22.Graph

// Adjacency list representation
noeq type graph = {
  num_vertices: nat;
  adj: array (list nat);  // adj[v] = list of neighbors
}

let graph_inv (g: graph) (edges: erased (set (nat * nat))) : slprop =
  A.pts_to g.adj #full_perm adj_lists **
  pure (Seq.length adj_lists == g.num_vertices) **
  pure (forall v u. (v, u) `Set.mem` edges <==> 
                    v < g.num_vertices /\ List.mem u (Seq.index adj_lists v))
```

**File:** `ch22-elementary-graph/BFS.pulse`

```pulse
fn bfs (g: graph) (s: nat{s < g.num_vertices})
  requires graph_inv g edges
  returns (dist: array (option nat), pred: array (option nat))
  ensures graph_inv g edges **
          A.pts_to dist #full_perm dist_seq **
          A.pts_to pred #full_perm pred_seq **
          pure (forall v. Seq.index dist_seq v == shortest_distance g s v) **
          pure (forall v. valid_predecessor pred_seq dist_seq g s v)
```

**File:** `ch22-elementary-graph/DFS.pulse`

```pulse
fn dfs (g: graph)
  requires graph_inv g edges
  returns (discovery: array nat, finish: array nat, pred: array (option nat))
  ensures graph_inv g edges **
          // Discovery and finish times form valid parenthesis structure
          pure (valid_dfs_timestamps discovery finish g)
```

**File:** `ch22-elementary-graph/TopologicalSort.pulse`

```pulse
fn topological_sort (g: graph)
  requires graph_inv g edges ** pure (is_dag g edges)
  returns order: list nat
  ensures graph_inv g edges **
          pure (is_permutation order (range 0 g.num_vertices)) **
          pure (forall u v. (u,v) `Set.mem` edges ==> 
                           list_index u order < list_index v order)
```

#### 5.2.7 Chapter 24: Single-Source Shortest Paths

**File:** `ch24-sssp/Dijkstra.pulse`

```pulse
module CLRS.Ch24.Dijkstra

// Weighted graph
noeq type weighted_graph = {
  num_vertices: nat;
  adj: array (list (nat * nat));  // (neighbor, weight) pairs
}

fn dijkstra (g: weighted_graph) (s: nat{s < g.num_vertices})
  requires wgraph_inv g edges ** 
           pure (all_weights_nonnegative g)  // Required for Dijkstra
  returns (dist: array nat, pred: array (option nat))
  ensures wgraph_inv g edges **
          A.pts_to dist #full_perm dist_seq **
          A.pts_to pred #full_perm pred_seq **
          pure (forall v. Seq.index dist_seq v == shortest_path_weight g s v)
```

**File:** `ch24-sssp/BellmanFord.pulse`

```pulse
fn bellman_ford (g: weighted_graph) (s: nat{s < g.num_vertices})
  requires wgraph_inv g edges
  returns result: option (array nat * array (option nat))
  ensures wgraph_inv g edges **
          (match result with
           | None -> pure (has_negative_cycle g s)
           | Some (dist, pred) -> 
               A.pts_to dist #full_perm dist_seq **
               pure (forall v. Seq.index dist_seq v == shortest_path_weight g s v))
```

### 5.3 Data Model / Schema

#### Directory Structure Per Chapter

```
ch<NN>-<name>/
├── README.md           # Chapter overview, algorithms covered, usage
├── <Algorithm>.pulse   # Main implementation
├── <Algorithm>.fsti    # Interface with specifications (if needed)
├── Predicates.fst      # Chapter-specific predicates
└── Tests.fst           # Test cases (if applicable)
```

#### Common Library Structure

```
common/
├── Predicates.fst      # Shared predicates (sorted, permutation, etc.)
├── Predicates.fsti     # Interface
├── ArrayOps.pulse      # Verified swap, copy, range operations
└── ArrayOps.fsti       # Interface
```

### 5.4 Algorithm Implementation Guidelines

1. **Signature Pattern:**
   ```pulse
   fn algorithm_name (inputs...) 
     requires ownership_predicates ** pure (preconditions)
     returns result_type
     ensures ownership_predicates ** pure (postconditions)
   ```

2. **Loop Invariant Pattern:**
   ```pulse
   while (condition)
   invariant exists* ghost_state.
     ownership ** pure (invariant_properties)
   { body }
   ```

3. **Ghost State Management:**
   - Use `erased` types for specification-only values
   - Bind existentials with `with witness. _`
   - Call lemmas for complex reasoning

4. **Memory Management:**
   - All `Box.alloc` must have matching `Box.free`
   - Transfer ownership explicitly through function boundaries
   - Use `drop_` only for empty resources

---

## 6. Alternatives Considered

| Option | Pros | Cons | Decision |
|--------|------|------|----------|
| **Pure F* (no Pulse)** | Simpler verification, no ownership tracking | Not imperative, can't demonstrate low-level algorithms | Rejected: Goal is to show verified imperative code |
| **LowStar/KaRaMeL** | Extractable to C, mature tooling | Older framework, not separation logic based | Rejected: Pulse is the modern approach |
| **Pulse (Selected)** | Separation logic, clean syntax, modern F* | Newer, less documentation | **Selected**: Best demonstrates current FStar capabilities |
| **External SMT hints** | Can help hard proofs | Fragile, non-portable | Use sparingly for complex invariants |

---

## 7. Cross-Cutting Concerns

### 7.1 Verification Strategy

- **Functional Specs:** Define using `FStar.Seq` and pure predicates
- **Separation Logic:** Use `pts_to` for ownership, `**` for composition
- **Invariant Proofs:** Establish loop invariants, prove maintenance
- **Termination:** Use decreasing measures (array indices, tree heights)

### 7.2 Testing Strategy

- **Type Checking:** All files must typecheck with `fstar.exe`
- **Extraction Testing:** Extract to OCaml/F# and run on test inputs
- **Property Testing:** Use QuickCheck-style tests where applicable

### 7.3 Documentation

Each chapter README.md must include:
1. Algorithm descriptions and complexity
2. Verification properties proved
3. Usage examples
4. References to CLRS sections

---

## 8. Migration, Rollout, and Testing

### 8.1 Implementation Phases

- [ ] **Phase 1 (Core Foundations):** Chapters 2, 6, 7, 10, 12, 21, 22, 24
  - Establishes fundamental patterns
  - Creates reusable predicates library
  - ~40 algorithms
  
- [ ] **Phase 2 (Advanced Structures):** Chapters 11, 13, 15, 18, 23
  - Hash tables, balanced trees
  - Dynamic programming patterns
  - ~25 algorithms

- [ ] **Phase 3 (Specialized):** Chapters 8, 9, 16, 26, 31, 32, 33
  - Linear sorting, selection
  - String matching, geometry
  - ~30 algorithms

- [ ] **Phase 4 (Advanced Topics):** Chapters 4, 14, 19, 20, 25, 28, 30, 35
  - Complex data structures
  - Numerical algorithms
  - ~25 algorithms

### 8.2 Verification Checklist Per Algorithm

- [ ] Compiles without errors
- [ ] Pre/post conditions specified
- [ ] Loop invariants proven
- [ ] Termination proven (if recursive)
- [ ] Memory safety verified (no leaks)
- [ ] README documentation written

### 8.3 Test Plan

- **Unit Tests:** Each algorithm has test cases
- **Integration Tests:** Data structures used by algorithms (e.g., heap in heapsort)
- **Regression:** CI verifies all files typecheck

---

## 9. Open Questions / Unresolved Issues

- [ ] **Randomized algorithms:** How to verify probabilistic guarantees (e.g., randomized quicksort expected O(n lg n))? Consider using probability monad or probabilistic relational Hoare logic.

- [ ] **Floating-point:** How to handle FFT and matrix operations with floating-point? Options: fixed-point arithmetic, or mark as "implementation only" without full verification.

- [ ] **Parallelism:** Should Chapter 27 (multithreaded) algorithms be attempted using Pulse's parallel constructs? Requires investigation of Pulse's concurrency support.

- [ ] **Amortized analysis:** Can we encode potential functions in F* to prove amortized bounds? Or focus on worst-case correctness only?

- [ ] **Extraction target:** Should we target OCaml extraction for testing, or also support C via KaRaMeL?

---

## 10. References

- **Research Document:** `research/docs/2026-02-05-clrs-algorithms-pulse-implementation-plan.md`
- **CLRS Textbook:** Cormen, Leiserson, Rivest, Stein. "Introduction to Algorithms", 3rd Edition, 2009
- **Pulse Documentation:** FStar `.github/agents/PulseCoder.md`
- **Existing F* Algorithms:** `FStar/examples/algorithms/` (QuickSort.Seq.fst, InsertionSort.fst, MergeSort.fst)
- **FStar Sequence Library:** `FStar/ulib/FStar.Seq.*`
