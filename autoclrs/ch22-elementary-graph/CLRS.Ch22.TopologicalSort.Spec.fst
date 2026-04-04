(**
 * CLRS Chapter 22: Topological Sort — Pure Functional Specification
 *
 * Defines what a topological order IS and proves key properties:
 *   - Topological order implies DAG (no cycles)
 *   - For all edges (u,v), u appears before v in the order
 *   - Helper functions for position lookup
 *
 * Zero admits.
 *)
module CLRS.Ch22.TopologicalSort.Spec

open FStar.Mul

(*** Graph Representation ***)

// Check if there's an edge from u to v in the adjacency matrix
let has_edge (n: nat) (adj: Seq.seq int) (u v: nat) : bool =
  u < n && v < n && 
  Seq.length adj >= n * n &&
  u * n + v < Seq.length adj &&
  Seq.index adj (u * n + v) <> 0

(*** Position in Order ***)

// Find the position of vertex v in the order sequence
// Returns None if v is not in order
let rec position_in_order_aux (order: Seq.seq nat) (v: nat) (pos: nat) 
  : Tot (option nat) (decreases (Seq.length order - pos))
  = if pos >= Seq.length order then None
    else if Seq.index order pos = v then Some pos
    else position_in_order_aux order v (pos + 1)

let position_in_order (order: Seq.seq nat) (v: nat) : option nat =
  position_in_order_aux order v 0

// Helper: check if u appears before v in order
let appears_before (order: Seq.seq nat) (u v: nat) : prop =
  Some? (position_in_order order u) /\
  Some? (position_in_order order v) /\
  Some?.v (position_in_order order u) < Some?.v (position_in_order order v)

(*** Topological Order ***)

//SNIPPET_START: is_topological_order
// A sequence is a topological order if:
// For every edge (u,v) in the graph, u appears before v in the order
let is_topological_order (adj: Seq.seq int) (n: nat) (order: Seq.seq nat) : prop =
  Seq.length order == n /\
  Seq.length adj == n * n /\
  (forall (u v: nat). has_edge n adj u v ==> appears_before order u v)
//SNIPPET_END: is_topological_order

(*** Path and Cycle Definitions ***)

// A path from u to v of length k exists
let rec has_path (adj: Seq.seq int) (n: nat) (u v: nat) (k: nat) 
  : Tot prop (decreases k)
  = if k = 0 then u == v
    else if k = 1 then has_edge n adj u v
    else exists (w: nat). w < n /\ has_edge n adj u w /\ has_path adj n w v (k - 1)

// A cycle exists: there's a path from some vertex u back to itself
let has_cycle (adj: Seq.seq int) (n: nat) : prop =
  exists (u: nat) (k: nat). u < n /\ k > 0 /\ k <= n /\ has_path adj n u u k

// A directed acyclic graph (DAG) has no cycles
let is_dag (adj: Seq.seq int) (n: nat) : prop =
  Seq.length adj == n * n /\ ~(has_cycle adj n)

(*** Distinctness and Validity ***)

// All elements in order are pairwise distinct
let all_distinct (order: Seq.seq nat) : prop =
  forall (i j: nat). i < Seq.length order /\ j < Seq.length order /\ i <> j ==>
    Seq.index order i <> Seq.index order j

// All elements in order are valid vertices (< n)
let all_valid_vertices (order: Seq.seq nat) (n: nat) : prop =
  forall (i: nat). i < Seq.length order ==> Seq.index order i < n

(*** Helper Lemmas for position_in_order ***)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"

// If position_in_order returns Some pos, then order[pos] == v
let rec lemma_position_in_order_correct (order: Seq.seq nat) (v: nat) (start: nat)
  : Lemma
    (requires start <= Seq.length order)
    (ensures (
      let result = position_in_order_aux order v start in
      (Some? result ==> (let pos = Some?.v result in 
                         pos >= start /\ pos < Seq.length order /\ Seq.index order pos == v)) /\
      (None? result ==> (forall (i: nat). start <= i /\ i < Seq.length order ==> Seq.index order i <> v))))
    (decreases (Seq.length order - start))
  = if start >= Seq.length order then ()
    else if Seq.index order start = v then ()
    else lemma_position_in_order_correct order v (start + 1)

// Corollary for position_in_order starting at 0
let lemma_position_correct (order: Seq.seq nat) (v: nat)
  : Lemma
    (ensures (
      let result = position_in_order order v in
      (Some? result ==> (let pos = Some?.v result in 
                         pos < Seq.length order /\ Seq.index order pos == v)) /\
      (None? result ==> (forall (i: nat). i < Seq.length order ==> Seq.index order i <> v))))
  = lemma_position_in_order_correct order v 0

// If order has distinct elements and v is in order, position_in_order finds it uniquely
let rec lemma_distinct_has_position_aux (order: Seq.seq nat) (v: nat) (pos: nat) (start: nat)
  : Lemma
    (requires 
      pos < Seq.length order /\
      start <= Seq.length order /\
      Seq.index order pos == v /\
      all_distinct order)
    (ensures (
      let result = position_in_order_aux order v start in
      if start <= pos 
      then result == Some pos
      else (Some? result ==> False)))
    (decreases (Seq.length order - start))
  = if start >= Seq.length order then ()
    else if start = pos then ()
    else if Seq.index order start = v then begin
      assert (Seq.index order start = Seq.index order pos);
      assert (start <> pos);
      ()
    end
    else lemma_distinct_has_position_aux order v pos (start + 1)

let lemma_distinct_has_position (order: Seq.seq nat) (v: nat) (pos: nat)
  : Lemma
    (requires 
      pos < Seq.length order /\
      Seq.index order pos == v /\
      all_distinct order)
    (ensures position_in_order order v == Some pos)
  = lemma_distinct_has_position_aux order v pos 0

#pop-options

(*** Main Theorems ***)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

#push-options "--z3rlimit 10"

// Transitivity of appears_before
let lemma_appears_before_trans (order: Seq.seq nat) (u v w: nat)
  : Lemma
    (requires appears_before order u v /\ appears_before order v w)
    (ensures appears_before order u w)
  = ()

// If there's a topological order and a path from u to v, then u appears before v  
let rec lemma_topo_order_path (adj: Seq.seq int) (n: nat) (order: Seq.seq nat) (u v: nat) (k: nat)
  : Lemma
    (requires 
      is_topological_order adj n order /\
      u < n /\ v < n /\
      k > 0 /\
      has_path adj n u v k)
    (ensures appears_before order u v)
    (decreases k)
  = if k = 1 then ()
    else
      // For k > 1, has_path gives us: exists w. edge(u,w) /\ path(w,v,k-1)
      let f (w: nat{w < n /\ has_edge n adj u w /\ has_path adj n w v (k - 1)})
        : GTot (squash (appears_before order u v))
        = lemma_topo_order_path adj n order w v (k - 1);
          lemma_appears_before_trans order u w v;
          ()
      in
      FStar.Classical.exists_elim
        (appears_before order u v)
        #nat
        #(fun w -> w < n /\ has_edge n adj u w /\ has_path adj n w v (k - 1))
        ()
        f

#pop-options

#push-options "--z3rlimit 10"
//SNIPPET_START: topo_order_implies_dag
// Main theorem: A topological order implies the graph is a DAG
let lemma_topo_order_implies_dag (adj: Seq.seq int) (n: nat) (order: Seq.seq nat)
  : Lemma
    (requires is_topological_order adj n order /\ n > 0)
    (ensures is_dag adj n)
//SNIPPET_END: topo_order_implies_dag
  = // Proof by contradiction using lemma_topo_order_path
    let aux (u: nat) (k: nat)
      : Lemma (requires u < n /\ k > 0 /\ k <= n /\ has_path adj n u u k)
              (ensures False)
      = lemma_topo_order_path adj n order u u k;
        // Now we have appears_before order u u
        let pos_u = position_in_order order u in
        assert (Some? pos_u);
        let p = Some?.v pos_u in
        assert (p < p)  // Contradiction
    in
    FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)
#pop-options

#pop-options

(*** Uniqueness Properties (assuming distinctness) ***)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"

// If topological order has distinct elements, each vertex has a unique position  
let lemma_topo_order_unique_position (adj: Seq.seq int) (n: nat) (order: Seq.seq nat) (v: nat) (pos1 pos2: nat)
  : Lemma
    (requires 
      is_topological_order adj n order /\
      all_distinct order /\
      pos1 < Seq.length order /\
      pos2 < Seq.length order /\
      Seq.index order pos1 == v /\
      Seq.index order pos2 == v)
    (ensures pos1 == pos2)
  = ()

// If order is distinct and valid, position_in_order works for all vertices
let lemma_distinct_valid_position (order: Seq.seq nat) (n: nat) (v: nat)
  : Lemma
    (requires
      Seq.length order == n /\
      all_distinct order /\
      all_valid_vertices order n /\
      v < n /\
      (exists (pos: nat). pos < n /\ Seq.index order pos == v))
    (ensures Some? (position_in_order order v))
  = FStar.Classical.exists_elim
      (Some? (position_in_order order v))
      #nat
      #(fun pos -> pos < n /\ Seq.index order pos == v)
      ()
      (fun pos -> lemma_distinct_has_position order v pos)

#pop-options
